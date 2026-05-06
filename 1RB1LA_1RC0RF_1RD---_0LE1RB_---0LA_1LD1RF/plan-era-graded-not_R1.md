# Plan: era-graded `OrbitReachable.not_R1`

**Status**: drafted 2026-05-05; ⚠️ **structural-fact gap discovered
2026-05-06** (see "Gap analysis" below); **BadShape framework + Option γ
scaffolding landed 2026-05-06** (see "Post-γ status" below); **path
forward consolidated to era-graded D2-spine bound** (Path 2 of three
rated options).

**Author note**: this plan replaces phase2.lean's per-shape backward
cascade (currently unbounded) with an era-graded *forward* argument
leveraging the Φ pipeline now in `phi.lean` / `phi_progress.lean` /
`phi_era.lean`. Stages A1+A2+B+C done in `era_orbit.lean`; Stage D
attempted 2026-05-06 — the underlying structural fact is **false** for
arbitrary `EraStartConfig`s (need orbit-reachability or a finer
invariant). IntraEraOf framework added in `era.lean` as infrastructure.

## Post-γ status (2026-05-06): consolidated path forward

After Option A landed (BadShape inductive predicate, `era_orbit.lean`
`BadShape.not_OrbitReachable`, 17 sorries → 4) and Option γ scaffolding
landed (`era_orbit_gamma.lean`, 333 L, axiom-clean), the residual goal
is **`BadShape.base R`**: `∀ R, ¬ OrbitReachable (M([], 3, R))`.

Three concrete paths were rated (see `plan-badshape.md`):

1. **Strictly-decreasing measure beyond Φ** (⭐⭐): blocked by Φ
   conservation along D2 (Δ=0) and unbounded cursor growth on D3.
   Worth a 1–2 hour parity-argument scout (cursor stays odd; init is
   even) before committing further.

2. **Era-graded D2-spine bound** (⭐⭐⭐⭐) ← **PRIMARY RECOMMENDATION**.
   This document's natural successor — see "Sub-plan E: D2-spine
   bound" below.

3. **F2 black-box** (⭐⭐): blocked on F2 conjecture itself being open.

### Available γ infrastructure (loadbearing for Path 2)

`era_orbit_gamma.lean` provides predecessor-uniqueness lemmas that any
era-graded D2-spine bound proof can build on:

- **γ.1 `macroStep_M_empty_3_predecessor_form`**: D2 is the **unique**
  macroStep producing `M([], 3, R)`. Predecessor is `M([2], 3, d::R')`
  with `R = 1 :: (d+1) :: R'`, k = 19.
- **γ.2 `macroStep_M_2list_3_predecessor_form`**: predecessors of
  `M(2 :: L_out, 3, R)` are either D2 extension
  (`M(2 :: 2 :: L_out, 3, d::R')`) or D3 lift
  (`M(1 :: L_out, 5, d::R')`).
- **γ.3 `gammaFuel cfg := cfg.phi - 6`**: Nat-valued fuel measure.
- **γ.4 `gammaSim`**: bounded forward simulator + preservation under
  OrbitReachable (`gammaSim_preserves_OrbitReachable`).

The cascade closure becomes (with γ.1/γ.2 as building blocks): given
orbit-reachable `M(L, c, R)` of cascade shape, recursively walk D2/D3
predecessors via γ.1/γ.2 until reaching either init (impossible by
parity / shape) or a config excluded by Φ. The era-graded structure
provides the FUEL that bounds the recursion.

## Sub-plan E: era-graded D2-spine bound (2026-05-06)

This is the consolidated successor to Sub-plans A–D and Option C-3,
incorporating γ.1/γ.2 infrastructure. Estimated **400–600 lines**.

### Strategy

1. **Define D2-spine length on cfg**:
   ```lean
   def d2SpineLen : MacroConfig → Nat
     | .M L 3 _ => L.length  -- if L is all-2s
     | _ => 0
   ```
   (refined version handles 2-spine prefix detection; full definition
    requires AllGe1 + element check).

2. **Bound D2-spine by intra-era sweep length**:
   ```lean
   theorem d2_spine_bounded_by_era {cfg : MacroConfig}
       (h : OrbitReachable cfg) (e : EraStartConfig)
       (he : IntraEraOf e cfg) :
       d2SpineLen cfg ≤ e.L.headD 0  -- bounded by era-start L head
   ```
   The sweep family preserves L (shifts only); D2's `sweep_and_shift`
   shrinks L by 1 per fire; D3's `sweep` preserves L size. So within
   one era, D2-spine length ≤ era-start `L.head`.

3. **Cross-era recursion**: era-grading's `phi_strict_between_era_starts`
   gives a Φ-strict descent across eras. After ≤ `(Φ - 6) / 4` cross-era
   steps, Φ < 6, contradicting `phi_ge_init`.

4. **Wire to `BadShape.base R`**:
   ```lean
   theorem BadShape.not_OrbitReachable_base {R : List Nat} :
       ¬ OrbitReachable (.M [] 3 R) := by
     intro h_or
     -- Walk D2-cascade backward via γ.1/γ.2
     -- Bound spine length via era-graded structure
     -- Reach init or Φ < 6: contradiction
     sorry
   ```

### Risks

- Step 2 (D2-spine bound) requires the inverse direction of the
  era-graded sweep theorem (forward: era-start L → end-of-era L;
  backward: end-of-era L → era-start L). The forward direction is
  available; the inverse may need new lemmas (~50–100 lines).
- Cross-era recursion requires `IntraEraOf` to be parameterised on
  era-start in a way that supports backward walk. `era.lean`'s
  IntraEraOf framework was added but not exercised for backward analysis.
- Stage D's failure (structural fact false) does NOT block this — Sub-plan E
  uses the orbit-reachable era-start set directly via Stage A2's Φ ≥ 6
  invariant, sidestepping the multi-L oscillation issue.

### Why the era-graded approach now

Pre-γ, the cascade was per-shape and unbounded. Post-γ, the predecessor
structure is **canonical** (γ.1 says D2 is the unique producer), so the
cascade reduces to a SINGLE recursive structure: walk D2/D3 backward
on shapes `M((2 ×× n), 3, R)` and `M(1 :: (2 ×× n), 5, R)`, bound by
era-graded length. No multi-shape Layer enumeration; the recursion is
linear in cascade depth.

## Gap analysis (2026-05-06)

Two concrete counterexamples within `EraStartConfig` show the plan's
"unique era-start = `M([1], 5, [1])`" structural fact does not hold
across the IntraEra trajectory:

**Counterexample 1 — multi-L drain**: `e = M([1, 2], 5, [1])` (Φ = 9):
1. sweep:           `M([1, 2], 5, [1])` → `M([2, 2], 3, [2])`
2. sweep_and_shift: `M([2, 2], 3, [2])` → `M([2], 3, [1, 3])`
3. sweep_and_shift: `M([2], 3, [1, 3])` → `M([], 3, [1, 2, 3])`

`e` is a valid `EraStartConfig`, distinct from `M([1], 5, [1])`, that
reaches intra-era `M([], 3, _)` after three macroSteps.

**Counterexample 2 — singleton-L oscillation**: `e = M([1], 13, [1])`
(Φ = 15, singleton L):
1. 5 sweeps:        `M([1], 13, [1])` → `M([6], 3, [6])`
2. sweep_and_shift: `M([6], 3, [6])` → `M([], 7, [1, 7])`
3. sweep_left_empty: `M([], 7, [1, 7])` → `M([1], 5, [2, 7])`
4. sweep:           `M([1], 5, [2, 7])` → `M([2], 3, [3, 7])`
5. sweep_and_shift: `M([2], 3, [3, 7])` → `M([], 3, [1, 4, 7])`

After Phase 0's `sweep_and_shift` empties `L`, the trajectory's cursor
≥ 4 case re-fills `L` via `sweep_left_empty`, restarting a new sweep
prefix at length 1 with R length 2. This **oscillation** (L between
[] and [1]) is the structural mechanism the plan missed.

### Implications

The plan's Phase-0-only analysis assumes the era's intra-era trajectory
ends at the first `M([], _, _)` shape. In reality, IntraEra (under pure
macroStep) continues across multiple sweep_and_shifts and even crosses
L=[] zero-cursors via sweep_left_empty. Multiple distinct era-starts
(of varying |L|) reach intra-era `M([], 3, _)`.

### Orbit-reachability rescue?

Counterexample 1 has Φ = 9, which violates the depth-1 lower bound
Φ ≥ 10 from `phi_strict_between_era_starts`. So **Counterexample 1 is
NOT orbit-reachable** (excluded by Stage A2.0 + jump bound).

Counterexample 2 has Φ = 15, which fits depth-2 (6 + 4·2 = 14 ≤ 15
< 18). Whether `M([1], 13, [1])` is *actually* orbit-reachable depends
on the orbit's specific era-start sequence. From init = `M([1], 4, [1])`,
the deterministic macroStep trajectory yields depth-1 era-start
`M([1], 10, [1])` (Φ=12). Depth-2+ era-starts require multi_bounce_*
firings, so they're not directly reachable via macroStep alone — but
the OrbitReachable predicate includes those constructors. Whether a
depth-2 era-start of shape `M([1], 13, [1])` arises is an empirical
question (era-sim's 63 K era-boundaries dataset can be queried).

**Conclusion**: Stage D is provable IF restricted to orbit-reachable
era-starts AND the set of orbit-reachable era-starts producing intra-era
`M([], 3, _)` is empty (or contains only non-orbit-reachable era-starts).
The plan's structural-derivation argument is **insufficient** to prove
this directly.

### Revised paths forward

1. **Sub-plan A**: Strengthen `phi_strict_between_era_starts` to
   characterize *exact* orbit-reachable era-start shapes (not just Φ
   bounds). Use `era-sim`'s recurrence patterns. Rules out specific
   shapes like `M([1], 13, [1])`. **Effort**: high (~200+ lines, requires
   modeling orbit dynamics).

2. **Sub-plan B**: Prove an additional invariant on intra-era
   trajectories that distinguishes Phase-0-only states from
   post-oscillation states. E.g., a quantity like `sum(R) - 1 ≥
   (era-start L's sum) − 1` or similar that grows across sweep_left_empty
   oscillations. **Effort**: medium (~80 lines if invariant exists).

3. **Sub-plan C** (recommended): **Pivot to Stage F via mutual induction
   with Φ pruning** of the phase2 cascade. Don't rely on Stage D's
   structural fact. Use Φ + per-rule deltas to bound the cascade depth.
   **Effort**: medium (~100 lines), already supported by the Φ
   pipeline. See `era_orbit.lean`'s `OrbitReachable.phi_ge_init`.

4. **Sub-plan D**: Maintain phase2.lean's manual cascade but extend it
   with Φ-based pruning to terminate. **Effort**: high (~300+ lines
   given current cascade state).

Recommendation: **Sub-plan C**. Φ may be sufficient to close the
phase2 cascade by ruling out shapes whose Φ value is below the depth
threshold for any era-start that could produce them.

## Sub-plan C analysis (2026-05-06): Φ-pruned phase2 cascade

Re-examined Sub-plan C in detail. Φ-pruning is **conceptually correct**
but the formalization is **more involved than initially estimated**.

### Termination analysis

Cascade preserves Φ along the **sweep family** (`sweep`, `sweep_and_shift`)
and **strictly decreases Φ** along the **M0-side** rules (`era_and_sweep_*`,
`zero_two_*`, `zero_bounce_*`). Sweep-family-only chains must terminate
because:
- Sweep backward: `L_head -1`, `R_head -1`. Bounded by `min(L_head, R_head)`
  initially.
- Sweep_and_shift backward: `L_head` becomes 2 (always), `R_head` removed,
  `R[1] -1`. After enough iterations, `R.sum` reaches its lower bound
  `R.length` (AllGe1), forcing AllGe1 violation.
- Combined: sweep-family chain length bounded by `O(R.sum + L_head)`.

After sweep-family terminates, only M0-side backward steps remain (Φ
strictly decreases by ≥ 2). After ≤ `(Φ - 6)/2` M0-side steps, Φ < 6,
excluded by `OrbitReachable.phi_ge_init`.

Total cascade depth: `O(R.sum + L_head + Φ)` — finite for any specific cfg.

### Concrete subcase (single-R) proof sketch

Closing `OrbitReachable.not_M_empty_3_R` for the **single-R subcase**
(`R = [d]`, `d ≥ 1`) is **already proven** (`era.lean`'s
`IntraEra.not_M_empty_3_single` + the existing `step_macro` case in
`OrbitReachable.not_M_empty_3`). The single-R case closes because
`macroStep_no_M_empty_3_single` rules out the only generator
(`sweep_and_shift` produces R length ≥ 2).

The remaining open case is **multi-R** (`R = d :: R'` with `R' ≠ []`).
Cascade chain for the simplest multi-R closure:

| Layer | Shape | Closure |
|-------|-------|---------|
| 0 | `M([], 3, R)` (multi-R) | step_macro pred = M([2], 3, …); other constructors output mismatch |
| 1 | `M([2], 3, R₁)` | step_macro pred ∈ {`M([2,2], 3, _)` if R₁[0]=1, `M([1], 5, _)` if R₁[0]≥2}; other mismatch |
| 2a | `M([2, 2], 3, R₂)` | recurse (same shape pattern, `L = [2,…,2]`) |
| 2b | `M([1], 5, R'_2)` | sweep backward L_head=0 invalid; M0-side preds (Φ decreases) |
| ... | ... | ... |

Each layer of the chain expands the predecessor set; phase2.lean has
already enumerated Layers 0–5 (predecessor lemmas). Closing requires
**outer induction on Φ (or another well-founded measure)** to handle
the recursion.

### Why ~100 lines was an underestimate

Each cascade closure lemma `OrbitReachable.not_S` requires:
- **12+ OrbitReachable constructor cases**: `init`, `step_macro`,
  `step_multi_bounce_general`, `step_multi_bounce_general_to_zero`,
  `step_multi_bounce_2_and_shift`, `step_multi_bounce_2_double_shift`,
  `step_multi_bounce_3run_last_2`, `step_multi_bounce_last_2_general`,
  `step_R2_zero`, `step_R2_succ`, `step_R3`, `step_R1`. Each requires
  showing the constructor's output shape ≠ `S` or recursing via IH.
- **Predecessor recursion via phase2's lemmas**: `step_macro` case
  invokes `macroStep_M_*_predecessor` which gives ≤ 6 predecessor
  shapes. Each predecessor shape needs its own `not_S'` lemma.
- **Φ-side condition handling for `step_R3`**: the constructor takes a
  Φ-equation as a side condition, requiring careful Φ arithmetic.

A realistic single cascade closure lemma is ~50-100 lines. The full
chain has ≥ 5 layers × 2-3 producers per layer = ~10-15 helper lemmas,
each ~50-100 lines = **600-1500 lines** of cascade closure code, plus
the well-founded recursion infrastructure.

### Concrete next-step lemmas (in dependency order)

Closing `OrbitReachable.not_M_empty_3_multi` (the multi-R case)
requires this chain:

```
not_M_empty_3_multi  (top, closes in era.lean's existing sorry)
├─ not_M_2_3 (multi-R)            -- layer 1
│  ├─ not_M_2_2_3 (multi-R)       -- layer 2a → recurses to layer 3
│  │  └─ ... (recursion)
│  └─ not_M_1_5 (multi-R)         -- layer 2b
│     ├─ not_M_empty_7 (multi-R)  -- branch point
│     ├─ not_M0_2_1 (Φ excluded)  -- ✅ already proved
│     ├─ not_M0_2_1_2 (Φ excluded) -- ✅ already proved
│     ├─ not_M0_2_1_2_d_R         -- requires recursion
│     └─ not_M0_1_1_4             -- requires Φ + other analysis
```

The full closure requires **well-founded recursion** on a measure like
`(Φ, sweep-chain-depth, |L|+|R|)` to handle the unbounded sweep-family
backward chain (e.g., `M([2,2,...,2], 3, _)` of arbitrary length).
Lean's `WellFoundedRecursion` or `Nat.strongRecOn` can support this,
but threading it through 12+ OrbitReachable cases per lemma is
substantial work.

### Recommendation (revised)

Sub-plan C is the right *direction* but a 2-3 week effort, not a 1-day
fix. Concrete pragmatic options:

**Option C-1** (incremental): Close just `not_M_empty_3_multi` using a
single nested induction, leaving the recursion explicit. Demonstrates
the pattern, ~300 lines.

**Option C-2** (infrastructural): Define a `BadShape` inductive
predicate as the closure of `M([], 3, R)` under `macroStep` predecessors,
then prove `OrbitReachable cfg → ¬BadShape cfg` via double induction.
Cleaner but requires careful design, ~400 lines.

**Option C-3** (hybrid): Use `IntraEraOf` framework + per-era boundary
analysis to short-circuit the cascade. Combine with phase2's Layer 0
lemma to prove `OrbitReachable cfg → cfg = .M [] 3 _ → False` via era
structure. Ties Sub-plan B and C together. ~250 lines if it works.
**Status (2026-05-06): SUPERSEDED by Sub-plan E above** (which is
Option C-3's natural maturation incorporating γ.1/γ.2).

**Option C-4** (defer): Mark R1 as a stable axiom, document the
intended closure, focus on other Pillai problems where progress is
faster. Document the empirical evidence (era-sim 63K boundaries with
no R1 trigger) as informal soundness witness.

---

## Original plan (preserved below for reference)


## Goal

Close the last reachability axiom `reach_M_nil_3` (R1) by proving:

```lean
theorem OrbitReachable.not_R1 {cfg : MacroConfig}
    (h : OrbitReachable cfg) :
    ∀ d R', cfg ≠ .M [] 3 (d :: R')
```

This makes the R1 axiom invocation in `progress.lean:macro_progress`
(line 58 — `exact reach_M_nil_3 hinv`) unreachable by an upstream
`OrbitProg → ¬ R1-shape` derivation, removing R1 from the axiom set.

## Key structural fact

> **Within any era's intra-era trajectory, the unique era-start that
> produces `M([], 3, _)` is `M([1], 5, [1])`.**

### Derivation

An `EraStartConfig` has `M(L, c, [1])` with `L ≠ []`, `AllGe1 L`,
`c ≥ 4`. Sweep-prefix dynamics from the era-start:

| step | shape | rule |
|------|-------|------|
| 0 | `M([a₀,…], c₀, [1])` | era-start |
| 1 | `M([a₀+1,…], c₀-2, [2])` | `macro_sweep` (or `_left_empty`/`_solo`) |
| 2 | `M([a₀+2,…], c₀-4, [3])` | sweep |
| … | | |
| n | `M([a₀+n,…], c₀-2n, [n+1])` | sweep |

Sweep prefix preserves `|L|` exactly. The prefix terminates when c
enters {2, 3}:
- **c₀ even**: prefix runs `(c₀-2)/2` steps, ending at c=2. Era exits
  via `sweep_to_zero` to an M0 phase. **Cannot produce M([], 3, _).**
- **c₀ odd ≥ 5**: prefix runs `(c₀-3)/2` steps, ending at c=3. Era
  exits via `sweep_and_shift` (the only L-shrinking rule).

At c=3 era-end, `sweep_and_shift` on `M(a::L', 3, d::R')` produces
`M(L', a+1, 1::(d+1)::R')`. For the output `L = []`, the input must be
`M([a], 3, _)` (singleton L). With the sweep prefix preserving `|L|`,
this means the era-start L was singleton: `L = [a₀]`.

After `(c₀-3)/2` sweeps from `M([a₀], c₀, [1])`:
```
M([a₀ + (c₀-3)/2], 3, [(c₀-3)/2 + 1])
```

`sweep_and_shift` produces:
```
M([], a₀ + (c₀-3)/2 + 1, 1 :: ((c₀-3)/2 + 2) :: [])
   = M([], a₀ + (c₀-3)/2 + 1, [1, (c₀+1)/2])
```

For the output cursor to equal 3 (the R1 trigger):
```
a₀ + (c₀-3)/2 + 1 = 3
⟺ 2·a₀ + c₀ = 7
```

With `a₀ ≥ 1` (AllGe1) and `c₀ ≥ 5` (odd): the unique solution is
`(a₀, c₀) = (1, 5)`. Era-start `M([1], 5, [1])`, output `M([], 3, [1, 3])`.

For era-starts with `|L| ≥ 2`, sweep_and_shift produces `M(L_tail, _, _)`
with `L_tail ≠ []`, so the R1 shape (L=[]) cannot occur within the era.

For era-starts with `c₀ even`, the era exits at c=2 via sweep_to_zero
(no L-drain possible). M([], 3, _) likewise unreachable within the era.

For era-starts with `(a₀, c₀) ≠ (1, 5)` and `|L|=1` (still odd c₀): the
output cursor `a₀ + (c₀-3)/2 + 1 ≠ 3`, so the produced shape `M([], _, _)`
is NOT R1 (cursor mismatch).

✓ The structural fact holds.

## Strategy

**Prove `M([1], 5, [1])` is not an orbit-reachable era-start.** Then by
the structural fact, no era's intra-era trajectory hits R1 — done.

The Φ pipeline gives this directly: `M([1], 5, [1])` has `Φ = 7`, but
non-init era-starts in the orbit have `Φ ≥ 10` (from
`phi_strict_between_era_starts`'s +4 jump). The init era-start is
`M([1], 4, [1])`, not `M([1], 5, [1])`. Hence `M([1], 5, [1])` is
unreachable as an era-start.

Combined with showing the orbit's other paths to M([], 3, _) (via
raw-run constructors `step_R1`/`step_R3`) close vacuously / by output
shape, this gives `OrbitReachable.not_R1`.

## Stages

### Stage A: Φ ≥ 6 + 4n bound on orbit-reachable era-starts

#### A1. Era predecessor map

Define a partial function relating each era-start in an orbit to its
immediate predecessor era-start (None for init):

```lean
-- Conceptual; concrete lemma forms below.
def OrbitReachable.eraPredecessor {e : EraStartConfig}
    (h : OrbitReachable e.toMacro) :
    Option (Σ (e_prev : EraStartConfig), OrbitReachable e_prev.toMacro)
```

Or stated as an existence + relation:

```lean
theorem orbit_era_start_pred_or_init {e : EraStartConfig}
    (h : OrbitReachable e.toMacro) :
    e.toMacro = .M [1] 4 [1] ∨
    ∃ (e_prev : EraStartConfig) (fuel : Nat) (L : List Nat) (k : Nat),
      OrbitReachable e_prev.toMacro ∧
      (macroEra fuel e_prev.toMacro).2 = .M0 L [1] ∧
      macroStep (.M0 L [1]) = some (k, e.toMacro)
```

**Difficulty**: medium. Requires inducting on OrbitReachable; for each
constructor, either it directly produces an era-shape (era_and_sweep_*,
zero_two_solo with `L_pre ≥ 2`, etc.) or it doesn't. Era-shape
producers must be wired through the era-predecessor relation.

**Edge cases**:
- `zero_two_solo`: `M0(a::L', [2]) → M(L', a+3, [1])`. Output L = L'.
  If |L_pre| = 1 (i.e., L' = []), output is `M([], a+3, [1])` — an
  era-shape with L=[], **NOT** an EraStartConfig (violates L_ne_nil).
  Such configs need separate handling (see Risks 3 below).
- `zero_bounce`: `M0(a::L', [z+5]) → M((a+4)::L', z+2, [1])`. Output
  cursor `z+2 ≥ 2`. For `z=0`: output cursor 2, NOT an era-start
  (`c_ge4` fails). For `z=1`: cursor 3, NOT era-start. For `z ≥ 2`:
  cursor ≥ 4, IS era-start.

This means the orbit visits configs of shape `M(_, c, [1])` with c < 4
that are not era-starts. These need to be classified separately or
shown to immediately leave era-shape via a single macroStep.

#### A2. Φ_n = 6 + 4n monotone bound

Statement:

```lean
theorem orbit_era_start_phi_lower_bound {e : EraStartConfig}
    (h : OrbitReachable e.toMacro) :
    ∃ n, e.toMacro.phi ≥ 6 + 4 * n ∧
         (n = 0 → e.toMacro = .M [1] 4 [1])
```

Or, more simply:

```lean
theorem orbit_era_start_phi_ge_init {e : EraStartConfig}
    (h : OrbitReachable e.toMacro) :
    e.toMacro.phi ≥ 6
```

Proof of the latter: induction via A1 + `phi_strict_between_era_starts`
(+4 per era step) + init has `Φ = 6`.

The stronger "+4n" form requires tracking n; useful but heavier.
Recommend: prove the simpler `≥ 6` first, add `+4n` only if needed.

**Lemmas used**: `phi_strict_between_era_starts` (already in
`phi_era.lean`).

**Difficulty**: medium (induction depends on A1 being clean).

### Stage B: M([1], 5, [1]) excluded as era-start

Statement:

```lean
theorem M_1_5_1_not_orbit_era_start :
    ¬ ∃ (e : EraStartConfig),
      e.toMacro = .M [1] 5 [1] ∧ OrbitReachable e.toMacro
```

Proof:
- `M([1], 5, [1])` has `Φ = 1 + 1 + 5 = 7`.
- If orbit-reachable as era-start at depth n, Stage A2 gives `Φ ≥ 6 + 4n`;
  with `Φ = 7`, n ≤ 0.25, hence n = 0.
- Init era-start is `M([1], 4, [1])`, distinct from `M([1], 5, [1])`
  (cursor mismatch).
- Contradiction.

**Difficulty**: low (~20 lines once Stage A2 is in).

### Stage C: M([1], 5, [1]) excluded from OrbitReachable

Lift Stage B to OrbitReachable directly, not just era-starts:

```lean
theorem OrbitReachable.not_M_1_5_1 {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M [1] 5 [1]
```

Proof requires: every orbit-reachable config of shape `M(L, c, [1])` is
either a properly-typed era-start (EraStartConfig) or one of the
"degenerate era-shapes" (L=[] from zero_two_solo, c<4 from zero_bounce).

The R1 path requires a *proper* era-start (c=5 ≥ 4, L=[1] ≠ []), so:
- `M([1], 5, [1])` IS a valid EraStartConfig.
- If orbit-reachable, by Stage A1 it's tied to an era-predecessor chain
  → applies Stage B → contradiction.

**Difficulty**: medium-high. Requires the full lift from OrbitReachable
to era-graded structure (Stage A1 result). The "degenerate era-shapes"
need not be excluded here; they don't match `M([1], 5, [1])`.

### Stage D: M([], 3, _) excluded intra-era given era-start ≠ M([1], 5, [1])

Statement:

```lean
theorem IntraEra.not_R1_unless_era_1_5_1 {cfg : MacroConfig}
    (h : IntraEra cfg) (e : EraStartConfig)
    (he_seed : ∃ k, (macroEra k e.toMacro).2 = cfg ∨ ...)  -- e seeds h
    (he_neq : e.toMacro ≠ .M [1] 5 [1]) :
    ∀ d R', cfg ≠ .M [] 3 (d :: R')
```

The exact statement form depends on how IntraEra tracks its era-start
seed. Likely cleanest: parameterize IntraEra over the seed era-start, or
use existential over era-starts.

Proof strategy: by induction on IntraEra, using:
- Sweep prefix shape derived from era-start (sweep_iter_M_cons_output
  in `era.lean` — already exists).
- The structural fact: only `(a₀, c₀) = (1, 5)` produces M([], 3, _).

Concretely:
- **`era_start` case**: era-start has R = [1] (length 1), R1 has length
  ≥ 1 with d::R'. Wait — `M([], 3, [1])` IS R1 with d=1, R'=[]. But the
  era-start has L ≠ [], so era-start ≠ M([], _, _). ✓
- **`step_within` case**: predecessor cfg₀ ∈ IntraEra; macroStep takes it
  to cfg. For cfg = M([], 3, _), the predecessor must be M([2], 3, _)
  (`macroStep_M_empty_3_predecessor` in phase2.lean). Now M([2], 3, _) is
  itself in IntraEra (by IH), and intra-era M([2], 3, _) requires the
  era-start L to be [1] (the unique value). Era-start cursor 5 (the
  unique value). Hence era-start = M([1], 5, [1]). Contradicts hypothesis.

The hard part: proving "intra-era M([2], 3, R) implies era-start =
M([1], 5, [1])". This needs the sweep-prefix uniqueness argument:
intra-era state (L, c, R) at fixed (L=[2], c=3) traces back via sweep
prefix to era-start (L=[a₀], c=c₀, [1]) with `a₀ + (c₀-3)/2 = 2`,
unique solution `(1, 5)`.

**Difficulty**: medium-high. Likely ~80 lines. The sweep-prefix backward
trace is the technical core.

#### D1. Helper: intra-era at c=3 with singleton L

```lean
theorem IntraEra.M_singleton_3_only_from_era_1_5_1
    {a : Nat} {R : List Nat} {cfg : MacroConfig}
    (h : IntraEra cfg) (hcfg : cfg = .M [a] 3 R)
    (e : EraStartConfig) (he_seed : ...) :
    e = ⟨[1], 5, ..., ..., ...⟩ ∧ a = 2 ∧ R = [(c₀-1)/2] -- or similar
```

This characterizes the unique era-start producing intra-era
M([a], 3, R) configurations.

### Stage E: Era-boundary outputs ≠ R1

Era-boundary transitions (`era_and_sweep`, `era_and_sweep_solo`,
`zero_two_solo`, `zero_bounce`, etc.) produce era-shape M(L, c, [1]).
For the produced shape to equal M([], 3, _), we'd need `[1] = d::R'`,
i.e., d = 1 and R' = []. This means cfg = M([], 3, [1]).

But era-boundary outputs typically have L ≠ [] (era_and_sweep family) or
specific c values. Going through dispatch:
- era_and_sweep / era_and_sweep_solo: output L ≠ [].
- zero_two_solo: output `M(L_pre_tail, a+3, [1])`. L_pre_tail = [] iff
  L_pre = [a]. Cursor a+3. For L_pre_tail = [] AND cursor = 3: a+3=3
  forces a = 0, violating AllGe1.
- zero_bounce: output `M((a+4)::L', z+2, [1])`. L always ≥ length 1.

So **no macro rule produces `M([], 3, [1])`** as an era-boundary
output. ✓

**Difficulty**: low (~20 lines, pure dispatch case-split).

### Stage F: top-level `not_R1`

```lean
theorem OrbitReachable.not_R1 {cfg : MacroConfig}
    (h : OrbitReachable cfg) :
    ∀ d R', cfg ≠ .M [] 3 (d :: R')
```

Proof by induction on OrbitReachable:
- **`init`**: `M([1], 4, [1]) ≠ M([], 3, _)`. (List.cons_ne_nil on L.)
- **`step_macro`**: predecessor cfg_pre, target M([], 3, d::R'). By
  `macroStep_M_empty_3_predecessor` (phase2.lean), `cfg_pre = M([2], 3, _)`.
  Now we need `OrbitReachable (.M [2] 3 _) → False`, which needs the
  IntraEra characterization: `M([2], 3, _)` is intra-era from era-start
  `M([1], 5, [1])` (Stage D1), which is excluded (Stage C).
- **`step_multi_bounce_*`**, **`step_R2_*`**: each produces a known
  shape; verify it's not M([], 3, _) by case analysis on the output.
- **`step_R1`**: predecessor is itself M([], 3, _). By IH on the
  predecessor, contradiction. (Vacuous case.)
- **`step_R3`**: cfg' has the side condition `(∀ R, cfg' ≠ .M [] 3 R)`
  baked into the constructor. Direct contradiction. (Vacuous case.)

**Difficulty**: medium (~50 lines once D and C are in).

### Stage G: wire-up — replace R1 axiom invocation

In `progress.lean:macro_progress`, the c=3 with empty L branch
(line 58: `exact reach_M_nil_3 hinv`) is dispatched only when the
config has shape M([], 3, d::R'). The OrbitReachable analog
`orbit_progress` (or `OrbitProg.advance`) can use
`OrbitReachable.not_R1` to conclude this case is unreachable, so the
axiom invocation is dead code.

```lean
-- In orbit_progress (the OrbitReachable version):
| 3, _ =>
    -- Need OrbitReachable hypothesis on the config
    -- not_R1 gives: cfg ≠ M([], 3, R), contradiction with the
    -- pattern match that put us in this branch.
    exact absurd rfl (h_orbit.not_R1 _ _)
```

After this wire-up, `reach_M_nil_3` axiom is removed from the build,
and `lean_verify Sweeper.sweeper_never_halts` should report only
`{propext, Classical.choice, Quot.sound}`.

**Difficulty**: low (~20 lines once `not_R1` is proved and the
OrbitReachable threading from `orbit_progress` is in place).

## Effort estimate

| Stage | Description | Lines | Difficulty |
|-------|-------------|-------|------------|
| A1 | Era predecessor map | ~80 | medium |
| A2 | `Φ ≥ 6` bound on era-starts | ~50 | medium |
| B  | M([1], 5, [1]) not era-start | ~20 | low |
| C  | M([1], 5, [1]) not orbit-reachable | ~50 | medium-high |
| D  | IntraEra M([], 3, _) only from M([1], 5, [1]) | ~80 | medium-high |
| D1 | helper: intra-era M([a], 3, R) characterization | ~50 | medium |
| E  | Era-boundary outputs ≠ R1 | ~20 | low |
| F  | Top-level `not_R1` | ~50 | medium |
| G  | Wire-up replace axiom invocation | ~20 | low |
| **Total** | | **~420 lines** | overall medium-high |

Estimated time: 2–3 days of focused work.

## Risks

1. **Stage A1 (Era predecessor lift)**. The orbit visits configs not
   neatly categorized as era-starts (L=[] from zero_two_solo at L_pre=[a],
   c<4 from zero_bounce at z<2). These need separate handling — likely
   showing they immediately leave era-shape via the next macroStep, so
   their successor IS an era-start (c ≥ 4) or back in the M0/sweep flow.
   The cleanest treatment may be enriching `EraStartConfig` to allow
   degenerate forms, or threading them through Stage A as
   "intermediate era-shape" cases.

2. **Step_R3 in OrbitReachable**. The constructor takes a raw-run witness
   without forcing the cfg' shape. Stage F's step_R3 case relies on the
   side condition `∀ R, cfg' ≠ .M [] 3 R`, already baked in — this is
   straightforward. But for **other shape exclusions** (e.g., M([1], 5, [1])
   excluded from cfg' outputs in Stage C) we'd need to inspect
   `forward_dynamics`'s output: `shift_to_macro_prog` produces shapes
   `M(L_after, _, [1])` with `L_after = R_mid_with_1_at_end.reverse ++
   (r' + 1) :: (a + 4) :: L'`, which always has `(a+4) ≥ 5` somewhere.
   So `L_after ≠ [1]` (L_after has length ≥ 3 at least), excluding
   `M([1], 5, [1])` form. Verify this in Stage C.

3. **Edge cases in IntraEra**. `zero_two_solo` and `zero_bounce` produce
   era-shape `M(L', c, [1])` with c possibly < 4. These don't fit
   EraStartConfig (`c_ge4` fails). The IntraEra step_within constructor
   excludes era-shape outputs (`hnot : ¬ ∃ L c, cfg' = .M L c [1]`), so
   these end the current IntraEra. They start a new era-shape segment
   that may not map cleanly to an EraStartConfig. Stage A1 must handle
   this: e.g., show that such "low-c era-shapes" still satisfy a Φ
   non-decrease property even if they're not full era-starts, or show
   their forward dynamics quickly produces a proper era-start.

4. **`OrbitReachable` constructors don't track era count**. Stage A2's
   "depth n" formulation requires reading the era count off the
   OrbitReachable derivation. If using existential ("∃ n, Φ ≥ 6 + 4n"),
   the bound is implicit. The simpler `Φ ≥ 6` form sidesteps this.

## Comparison to phase2 cascade

| Approach | Lines | Status | Bounded? |
|----------|-------|--------|----------|
| `phase2.lean` per-shape backward cascade | ~1364 (~50% of which is R1 cascade Layers 0–5) | ongoing, branches unboundedly | ❌ No: sweep family proliferates |
| Era-graded forward (this plan) | ~420 | drafted | ✅ Yes: depth-1 era enumeration |

The transformative win is shifting from per-shape backward enumeration
(unbounded via sweep family) to era-graded forward analysis (finitely
many era-starts, each excluded by Φ + structure).

## Files touched

| File | Modification | Stage |
|------|--------------|-------|
| `phi_era.lean` (or new `phi_orbit.lean`) | extend with A1, A2 | A |
| `era.lean` | extend with C1 (era-shape lift), D, D1, E | C, D, E |
| `progress.lean` (or new `not_R1.lean`) | F (top-level not_R1) and G (wire-up) | F, G |
| `progress.lean:macro_progress` | replace `reach_M_nil_3 hinv` with `not_R1`-derived contradiction | G |
| `phase2.lean` | unchanged; cascade lemmas can stay or be removed once R1 closes | — |

## Cross-references

- LOG.md "Φ tape-mass invariant" section + Stage 5 completion (2026-05-05).
- `phi_era.lean:phi_strict_across_era_step` and
  `phi_era.lean:phi_strict_between_era_starts` — the +4 jump used in A2/B.
- `era.lean:macroStep_M_intra_era_preserves_L_ne_nil` — sweep prefix
  preserves L (used in D's sweep-prefix backward trace).
- `era.lean:sweep_iter_M_cons_output` — explicit n-sweep iteration form.
- `era.lean:IntraEra.M_R_one_is_era_start` — era-shape ⟹ era-start (for
  proper `c ≥ 4` cases).
- `era.lean:macroStep_M0_R1_produces_era_start` — every M0(L, [1])
  macroStep output is an era-start (with `c ≥ 4`).
- `forward_dynamics.lean:thm_reach_multi_bounce_last_2_long_safe` —
  R3-narrow output excludes `M([], 3, R)` (used in Stage F step_R3 case).
- `phase2.lean:macroStep_M_empty_3_predecessor` — Layer 0 backward step
  (used in Stage F step_macro case).

## Next concrete step

Start with Stage A1's era predecessor lemma. This is the foundation
everything else rests on. Decompose into sub-cases by OrbitReachable
constructor; identify which constructors land on an `EraStartConfig`
shape vs. a degenerate era-shape (low-c or empty-L); handle each.

Once A1 + A2 are clean, Stages B and the rest fall into place quickly.
