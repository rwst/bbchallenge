# Plan: closing R1 via "reachable ∧ c = 3 → L ≠ []"

Companion to `era_findings.md`, `invariant_strategy.md`, `LOG.md`. Targets
the only remaining custom axiom `Sweeper.reach_M_nil_3` after R2 and
R3-narrow were closed (2026-04-29). The goal is form A.3 from
`invariant_strategy.md`: a structural-exclusion claim on the reachable set.

## Lean target

The axiom currently asserted in `machine.lean`:
```lean
axiom reach_M_nil_3 : ∀ (d : Nat) (R' : List Nat),
  ∃ k > 0, ∃ cfg, raw_iterate k (toRawConfig (.M [] 3 (d :: R'))) = cfg ∧
                  IsMacroProgConfig cfg
```

We replace this with a **theorem** by proving:

```lean
theorem OrbitReachable.not_R1 {d : Nat} {R' : List Nat} :
    ¬ OrbitReachable (.M [] 3 (d :: R'))
```

Then `sweeper_never_halts`'s axiom branch for the `M([], 3, _)` shape uses
`absurd hreach OrbitReachable.not_R1` instead of `reach_M_nil_3`. Same
template `phase2.lean` already follows for `not_R2` / `not_R3_narrow`.

## Why direct bridging fails

`reach_M_nil_3` cannot be proved as a constructive theorem (the way R2 and
R3-narrow were closed) because **M([], 3, R) literally halts**: raw-TM trace
from `M([], 3, [1])` reaches the undefined `C, 1` transition at step 31.
So there's no clean macro config to bridge to. The only Lean-level path is
unreachability — proving `OrbitReachable (M [] 3 (d :: R')) → False`.

Empirical sanity check: simulator confirms zero R1 firings in 6.2 × 10¹⁶
raw steps (era 63 K). The structural claim is true; proving it is the
challenge.

## What's already done (`phase2.lean`)

| Tier | Content | Status |
|------|---------|--------|
| 1 | Trivial corollaries of `OrbitReachable.macroInvariant` | ✅ |
| 2 | `init ≠ R1`, `init ≠ M0`, `init ≠ M([], _, _)` | ✅ |
| 3a–3d | M0 halt-pattern / R[0] / R-empty / cursor exclusions | ✅ |
| 3e–3h | Layer 0: `M([], 3, _)` predecessors → `M([2], 3, _)` only | ✅ |
| 3i | Layer 1: `M(2 :: _, 3, _)` producers (2 producer shapes) | ✅ |
| 3j | Layer 2: `M(1 :: _, 5, _)` producers (6 producers + 2 dead-ends) | ✅ |
| 3l | Layer 2 top-level + 8 Layer-3 lemmas | ✅ |
| 3m | Layer 3: 8 producer lemmas (4a–4d done; 4e–4h via master case-split) | ✅ |
| Layer 4 | 8 new shapes from Layer 3, partly done (e.g. `M([2,6],3,_)`) | ✅/partial |
| Layer 5 | recursive shapes — `M(1::1::1::_,3,_)`, `M([2,6],3,_)`, `M([5],5,_)`, `M0([2,6],_)`, etc. | ❌ open |
| 6 | wire-up replacing `reach_M_nil_3` invocation | ❌ |

The cascade is finite-branching at each layer but the wiki entry warns it
"branches unboundedly" past Layer 4. Brute extension is therefore not the
plan; we need either a closed form or a stronger invariant.

### Empirical cascade audit (Layer 5–6)

A walk-through of Layer 5's existing lemmas shows where new shapes open vs.
fold back into prior layers:

| Layer-5 shape | Producer reduces to |
|---|---|
| `M(1 :: L_out, 3, _)` | `M(2::1::L_out, 3, _)` (folds into Layer 1) **or** `M([], 5, _)` (NEW) |
| `M([2], 2, [3])` | `M([1], 4, [2])` (NEW) |
| `M([3], 2, [1])` | dead-end (invariant violation) |
| `M([3], 2, 1::d::R'')` | `M([1, 3], 3, _)` (folds into Layer 5(1)) |
| `M0([2], [6])` | `M([1], 2, [5])` (NEW) |

Layer 6 thus opens 3 new shapes (`M([], 5, _)`, `M([1], 4, [2])`,
`M([1], 2, [5])`). Tracing each one's predecessors gives 5+
producers per shape (sweep_and_shift from `M([4], 3, _)`, multiple M0
rules, etc.), and each of those is itself parameterized.

Empirically the reduction from `M([], 5, [1])` is concrete and tight
(verified by raw-TM simulation):

```
M([], 5, [1]) →[17 raw] M([1], 3, [2])      (sweep_left_empty)
  →[19 raw]  M([], 2, [1, 3])               (sweep_and_shift, drains L)
  →[11 raw]  M0([1], [2, 3])                (sweep_to_zero_left_empty)
  →[8 raw]   M([], 4, [4])                  (zero_two)
  →[15 raw]  M([1], 2, [5])                 (sweep_left_empty)
  →[11 raw]  M0([2], [6])                   (sweep_to_zero)
  → … cascade continues into Mersenne family
```

So Layer 6's new shapes are exactly the orbit-trace continuation of Layer 5's
new shape `M([], 5, _)`. The cascade is *threaded along the Mersenne-style
halting cursor sequence* `c ∈ {3, 7, 15, 31, ...}` — each "bad" cursor opens
its predecessor `M([], 2c+1, _)` etc.

Conjecture: the cascade closes iff every reachable Mersenne-like predecessor
sequence folds back to a finite set of shapes already excluded by
`MacroInvariant` or by `init`. Phase 2's Layer 4 was the first place a
**folding** occurred (e.g., shape `M(2 :: L_out, 3, _)` → producer
`M(2 :: 2 :: L_out, 3, _)` is Layer 1's same target with a shifted prefix).
If the **NEW** shapes opened at each subsequent layer eventually all fold
back, the cascade is finite. **This is the central open question.**

## Two structural facts that can break the cascade

### Fact A (cheap; immediately usable). `M(_, 1, _)` is unreachable.

**Claim.** `OrbitReachable (.M L 1 R) → False`.

**Why.** Inspection of every macroStep rule shows the output cursor is
always `≥ 2` *except* the `shift` rule, which itself fires only when
the input cursor is `1`. So `c = 1` is a fixed point: it cannot enter
the orbit unless it's already in. Combined with `init.c = 4`, no
reachable config has `c = 1`.

**Proof sketch (Lean).** Induction on `OrbitReachable`. Base: init is
`M [1] 4 [1]`, c = 4 ≠ 1. Step: assume cfg has reachable c ≥ 2 (IH); show
`macroStep cfg = some cfg' → cfg'.c ≥ 2`. Case-split on the macroStep
output shape; every rule outputs `c ≥ 2`. Note `shift` outputs `c = L[0]`
where `L[0] ≥ 1` by `MacroInvariant`'s `AllGe1 L` — but that allows `c = 1`
*if and only if `L[0] = 1`*. Two ways to handle:

- (a) Treat `shift` as the only "dangerous" rule and require its input has
  `c = 1`. By IH input c ≥ 2, so `shift` doesn't fire. (✓ clean.)
- (b) Strengthen the IH to "c ≥ 2 ∧ (c = 2 → L's first run isn't a 1 in
  that position) …". (avoids cascade.)

Path (a) is direct and short — likely ~30 lines of Lean.

**Why this matters for R1.** Layer-1 of the cascade (in `phase2.lean`)
identifies M([2], 3, R') and M([3], 1, R') as the two producers of
M([], 3, R). Fact A immediately discharges the second producer
(`M([3], 1, R')` has c = 1, unreachable). That collapses the cascade
to a single linear chain: only `M([2], 3, R')` matters.

### Fact B (the big lever). The "absorbing" sub-structure of c.

The macro rules partition by output cursor parity / value:

- `shift` is the *only* rule producing `c = 1`, and only when `L[0] = 1`.
  By Fact A, never reachable.
- `sweep_to_zero` / `zero_bounce_to_zero` are the only producers of the
  M0 kind. Their "c" is 0 by convention.
- All other M-output rules produce `c ≥ 2`, with the stronger property
  that `c ≥ 2` is *strictly* preserved by `sweep` (output c = c - 2
  for input c ≥ 4 — i.e., even-decrement).

**Observation (empirical, testable in Lean).** Within an era, sweeps
strictly decrement c by 2 until c ∈ {2, 3}. At c = 2, sweep_to_zero
fires (output M0). At c = 3, sweep_and_shift fires (requires L ≠ [];
otherwise R1).

So the only way to enter `M([], 3, R)` is to have entered some M-state
with `c ≥ 3, c odd, L = []` and then sweep down to c = 3. The sweep's
`sweep_left_empty` rule outputs `L = [1]` (non-empty!), so once L
becomes empty in one configuration and we sweep, L immediately
becomes [1]. Therefore **L can only be empty at c-values where no
sweep has fired since the last time L was emptied**.

This suggests an invariant of the form:

> `Safe : MacroConfig → Prop`
> `Safe (.M L c R) := c ≥ 2 ∧ (L = [] → c is_even ∧ c ≥ 4 ∧ ...)`

That is: when L is empty, c is even and ≥ 4 — so the next sweep brings
us to (L = [1], c - 2) without ever touching c = 3 or c = 1.

The empirical L_emptyness data confirms this — L is never empty at any
era boundary. The question is whether L ever becomes empty *during* an
era. (Answer: it does in `sweep_left_empty`'s post-state, transiently,
but only at c ≥ 4 even values; sweep then immediately re-populates.)

## Primary plan: A.3 via three-clause Safe predicate

### Step 1 — Extend `MacroInvariant` to a `Safe` predicate (1–2 days).

```lean
def Safe : MacroConfig → Prop
  | .M L c R =>
      MacroInvariant (.M L c R) ∧
      c ≥ 2 ∧                            -- Fact A
      (L = [] → 2 ≤ c ∧ Even c) ∧         -- L-empty only at even c ≥ 2
      (L = [] → c ≠ 2)                    -- and c ≥ 4 (combine into c ≥ 4 ∧ Even c)
  | .M0 L R => MacroInvariant (.M0 L R)   -- M0 unchanged
```

Where `Even c` means `∃ k, c = 2 * k`. (Possibly drop `Even` if it
makes preservation harder; the L = [] → c ≥ 4 alone is enough to block
R1, since R1 needs c = 3.)

### Step 2 — `Safe (init)` (5 lines).

`Safe (.M [1] 4 [1])` — L = [1] ≠ [] so the conditional is vacuous;
c = 4 ≥ 2; rest by `MacroInvariant.init`.

### Step 3 — `Safe cfg → ∀ cfg', macroStep cfg = some cfg' → Safe cfg'` (3–5 days).

Case-split on cfg's shape and the firing rule (≈ 22 cases, mirroring
`macro_progress`). Each case shows the output's `Safe` clauses follow
from the input's. Key cases:

- **`shift`** (input c = 1): doesn't fire by Fact A (input c ≥ 2 ⇒ c ≠ 1).
  Either invoke `not_M_c_1` (Tier 3c is already proved!) or absurd by
  `Safe.c ≥ 2`.
- **`sweep`** (M, c ≥ 4): output c = c - 2 ≥ 2. Output L = [L[0]+1, …]
  if input L non-empty, else [1]. Either way L ≠ []. So output `Safe`'s
  conditional is vacuous. ✓
- **`sweep_to_zero`** (M, c = 2): output kind = M0, conditional drops out. ✓
- **`sweep_and_shift`** (M, c = 3 with L non-empty): need `Safe (.M L 3 R)`
  to imply input L ≠ []. With the L-empty clause, *if input L = [] and c =
  3, then by `(L = [] → c ≥ 4)` we'd need `3 ≥ 4`, contradiction.* So
  `Safe ⇒ L ≠ []` at c = 3. Output L = L[1:] of input L of length ≥ 1; could
  be empty. **But** output c = L[0] + 1 ≥ 2; if output L = [] we need to
  check the empty-L clause: output c = old L[0] + 1 ≥ 2. We need
  output c = old L[0] + 1 ≥ 4 when output L = []. This forces
  **`Safe` should also say "c = 3 ∧ |L| = 1 → L[0] ≥ 3"**, i.e., L is
  not [1] or [2] when at c = 3 about to sweep_and_shift.

That last addendum is the rub — preserving it cascades again. So:

### Step 4 — Test for cascade explosion early.

Before sinking days into Step 3, write down all the *added* clauses
needed to make Step 3 close, and check whether they themselves cascade.
Concretely:

- **clause C1**: L = [] → c ≥ 4 (so c ≠ 3).
- **clause C2**: c = 3 ∧ |L| = 1 → L[0] ≥ 3 (avoid sweep_and_shift draining L).
- **clause C3**: c = L[0] (after `shift` ✗ already excluded), or in M0
  rules: producer of M(c = 3) with L = [old_L[0]+1] etc. — check each.

If C1+C2 are sufficient and self-preserving, **plan succeeds**.
If C2 forces a C3 forces a C4 …, fall back to Strategy B below.

### Step 5 — Wire-up (½ day).

Use `Safe` to dispatch the `M([], 3, R)` axiom branch in
`OrbitReachable.not_R1`:

```lean
theorem OrbitReachable.not_R1 {d : Nat} {R' : List Nat} :
    ¬ OrbitReachable (.M [] 3 (d :: R')) := by
  intro h
  have hsafe := h.safe
  have : (3 : Nat) ≥ 4 := hsafe.L_empty_implies_c_ge_4 rfl
  omega
```

## Strategy B — fallback if cascade explodes

### B.1 — Era-graded invariant (form C.5)

Tag each reachable config with its "era index" plus its position within the
era (number of sweeps done since era start). Within an era, configs follow
the linear chain `M(L_0, c_0, [1]) → M(L_0', c_0 - 2, [1]) → …` where L_0
grows by `(c_0 - 2)/2` and c_0 decreases by 2 each step. Then:

- intra-era invariant: simple — sweep-only dynamics.
- inter-era invariant: era_and_sweep / multi_bounce_general transitions
  between era-boundary shapes `M(L, c, [1])`. Era boundary shapes always
  have L ≠ [] (proved by intra-era arithmetic).

This is a heavier refactor (introduces era-index ghost field) but the era
data file `era_full.jsonl` is precisely the trace this refactor needs.

### B.2 — Reflection / native-decide bounded prefix

Run the macro orbit for N steps using `native_decide`, certify that none
of the first N steps reaches `M([], 3, _)`, and combine with a periodicity
argument. Doesn't work alone (orbit is non-periodic at era boundaries),
but could discharge a finite "tail" if the cascade can be reduced to a
finite set.

## Risk assessment (revised after Layer 5–6 audit)

| Path | Time est. | Risk |
|------|-----------|------|
| Fact A only (`OrbitReachable.M_cursor_ge_2`) | done — already in `progress.lean` | — |
| Strategy A — C1 alone | rules out 0 cases beyond what cascade already does; cascade still needed for `M([2], 3, _)` and `M(1::_, 3, _)` shapes. Net value: low. |
| Strategy A — full cascade closure (Layers 5–8+) | 2–6 weeks | Unknown — depends on whether new-shape opening converges (current audit suggests it follows the Mersenne family `c = 5, 7, 11, 15, …`, finite per layer but each layer adds 1–3 NEW shape families). |
| Strategy B (era-graded invariant) | 3–4 weeks | Heavy refactor of `OrbitReachable` framework but cleanly bounded — uses the era data we have. Likely faster total than A in practice. |
| Strategy A + B hybrid | 4–8 weeks | Best confidence path. |

The original plan's "C1 alone closes if no cascade" hypothesis was checked
during this update and **doesn't hold**: the cascade hits new opened
shapes at every layer past 4, not just C2's `c = 3, |L| = 1` constraint.
C1 is necessary but far from sufficient.

## Recommended execution order (revised)

Given the Layer 5–6 audit, the cleanest near-term path is **Strategy B**
(era-graded). Strategy A's cascade closure is open-ended; B's refactor is
bounded and uses the era dataset we already have.

### Strategy B — era-graded execution outline

1. **Week 1**: Define `EraStartConfig := { L : List Nat // L ≠ [] }` and
   `Reach_era : List Nat → Nat → Prop` characterizing reachable era-start
   shapes `M(L, c, [1])`.

2. **Week 1–2**: Prove that the **within-era trajectory** from `M(L, c, [1])`
   with `|L| ≥ 1, c ≥ 4` does not pass through `M([], 3, R)`. Concretely:

   - The first phase is `(c-3)/2` or `(c-2)/2` sweeps (each: c ← c-2,
     L[0] ← L[0]+1, R[0] ← R[0]+1).
   - At c ∈ {2, 3}, dispatch to `sweep_to_zero` or `sweep_and_shift`.
   - `sweep_and_shift` requires L ≠ [], which holds since sweeps preserve
     L's non-emptiness (no rule shrinks L during a sweep).
   - After the era's terminating `era_and_sweep` step, we land at a new
     era-start shape `M(L', c', [1])` with `|L'| ≥ 1` and `c' ≥ 4`
     (provable arithmetically from the within-era macro dispatch).

3. **Week 2–3**: Strengthen `OrbitReachable` to track era index, OR: define
   `OrbitReachable_at_era_start` for era-start shapes only. Prove that every
   `OrbitReachable cfg` with `cfg.kind = M, cfg.R = [1]` is era-start, and
   that intra-era configs differ from era-start by a bounded sequence of
   sweeps — none of which is `M([], 3, R)`.

4. **Week 3–4**: Wire up `OrbitReachable.not_R1` from the era-graded
   invariant; replace `reach_M_nil_3` invocation in `macro_progress`'s
   M([], 3, _) branch with `absurd hreach OrbitReachable.not_R1`.

### Strategy A — fallback if B's refactor proves infeasible

Continue Phase 2 cascade Layer-by-Layer, with the additional rule that any
new shape opened at Layer N is checked against the orbit's structural
constraint `c ≥ 2`, `kind = M0` requires `L ≠ []`, etc. Empirically observe
when the new-shape opening rate drops to zero. If it does (e.g., by Layer
12 or 15), the cascade closes naturally.

This is risky open-ended work; budget weekly status checks.

## Validation milestones

- **Build green** at each step (`lake build Sweeper`).
- **Axiom hygiene**: `#print axioms` shrinks from
  `[propext, Classical.choice, Quot.sound, reach_M_nil_3]` to
  `[propext, Classical.choice, Quot.sound]` only — closing the
  Sweeper TM completely.
- **No regression** on R2 / R3-narrow closures already in `phase2.lean`.

## Why Strategy B (era-graded) is more promising

The cascade in `phase2.lean` Layers 0–4 builds backward from the bad
shape, opening new shapes at each layer (per the Layer 5–6 audit above).
The Safe-predicate approach (Strategy A) turns it forward but discovers
*the same set of clauses* as the cascade — both approaches enumerate
the orbit's finite-fragment Mersenne predecessor sequence.

Strategy B's pivot: instead of chasing predecessors of the bad shape,
**characterize the entire reachable orbit**. The orbit consists of:
- intra-era sweep chains starting from `M(L, c, [1])`, ending at either
  `sweep_to_zero` (even `c`) or `sweep_and_shift` (odd `c`)
- inter-era transitions via `era_and_sweep`/multi_bounce_general /
  zero_bounce_to_zero etc., all producing the next era-start shape

Both phases avoid `M([], 3, R)` for **structural** reasons unrelated to
backwards predecessor enumeration:
- intra-era: every sweep keeps `L` non-empty
- inter-era: every era-end rule produces output with `L ≠ []` (verifiable
  by case-split on the rule's output shape)

Empirical support: 6,478 R3 firings, 0 R1 firings, 63 K era boundaries,
all `L ≠ []` and `c ≥ 4`. The era dataset (`era_full.jsonl`) is
exactly the trace this strategy formalizes.

## Today's verdict

The cascade approach is a multi-week-to-month effort with no convergence
guarantee. The era-graded approach is a 3–4 week refactor with a clear
endpoint. Strategy B is the recommended path.

Closing R1 is open work; today's contribution was scope clarification
and empirical evidence for the structural claim.
