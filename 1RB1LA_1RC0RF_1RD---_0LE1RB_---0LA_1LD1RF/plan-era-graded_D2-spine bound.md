# Sub-plan E: era-graded D2-spine bound

**Status**: drafted 2026-05-06; primary path forward post-γ scaffolding;
parity scout (`scout_parity.lean`) confirmed pure-parity insufficient,
elevating this plan to the unique remaining structural option.

**Goal**: close `BadShape.base R` in `era_orbit.lean:493`, i.e.
```lean
theorem OrbitReachable.not_M_empty_3 {R : List Nat} :
    ¬ OrbitReachable (.M [] 3 R)
```
which discharges `BadShape.not_OrbitReachable` and, in turn, all
remaining R1-shape exclusions (`OrbitReachable.not_M_empty_3_full`,
`step_R1` cases in `era_shape_phi_strict_predecessor`, `phi_ge_init`,
`not_M_1_5_1`).

This is the **last residual sorry** keeping `reach_M_nil_3` (R1) in the
axiom set. After E lands, `Sweeper.sweeper_never_halts` should depend
only on `{propext, Classical.choice, Quot.sound, reach_multi_bounce_*}`
(the latter pair already targeted for closure separately).

---

## 0 · Context: what γ delivered, what's left

`era_orbit_gamma.lean` (333 L, axiom-clean) provides:

| Lemma | Statement (informal) | Use |
|-------|---------------------|-----|
| **γ.1** `macroStep_M_empty_3_predecessor_form` | macroStep cfg = some(_, M([], 3, R)) ⇒ cfg = M([2], 3, d::R'), R = 1::(d+1)::R', k = 19 | base case of D2-cascade |
| **γ.2** `macroStep_M_2list_3_predecessor_form` | macroStep cfg = some(_, M(2::L_out, 3, R)) ⇒ cfg = M(2::2::L_out, 3, _) (D2) ∨ cfg = M(1::L_out, 5, _) (D3) | inductive step of D2-cascade |
| **γ.3** `gammaFuel`, `gammaFuel_macroStep_nondec` | fuel := Φ - 6; non-decreasing under macroStep | future fuel-walk; **not central to E** |
| **γ.4** `gammaSim`, `gammaSim_preserves_OrbitReachable` | bounded forward simulator | optional: forward-direction crosscheck |

**What is still needed.** γ.1/γ.2 only handle the leftmost two cascade
shapes (`M([], 3, R)` and `M(2::L_out, 3, R)`). The cascade is

```
M([], 3, R) ←D2─ M([2], 3, R₁) ←D2─ M([2,2], 3, R₂) ←D2─ … ←D2─ M([2ⁿ], 3, Rₙ)
                  ↑ D3 lift          ↑ D3 lift                    ↑ D3 lift
                  M([1], 5, R₁')     M([1,2], 5, R₂')           M([1, 2ⁿ⁻¹], 5, Rₙ')
                                                                  ↑ further D5/M0 layers
```

The parity scout established:
- **Within the M-side cascade**, every backward step lands on cursor ∈ {3, 5} with L of the form `(some prefix) ++ [2,2,...,2]`. This is closed under predecessor.
- **The cascade exits to M0-land** only at layers where L_head ≥ 5 (via D11 with z=1) — never at the canonical D2-spine shape.

So the cascade is structurally "tame" — its M-side is a *single
recursive shape pattern* — but it is leftward-unbounded (no a priori
bound on cascade depth n). The era-graded approach below provides the
**finite fuel** that tames the recursion.

---

## 1 · Strategy: era-grading provides the fuel

### Key observation

Every D2 backward step inserts a `2` at the front of L, growing
`d2SpineLen` by 1. Every D3 lift turns a `2`-prefixed L into a
`1`-prefixed L (a "spine break"). Every M0→M crossing requires
non-trivial L (head ≥ 5).

Within a single era, sweep dynamics preserves `|L|` (sweep family) or
shrinks it by 1 per fire (sweep_and_shift). So the **D2-spine length
within an era is bounded by the era-start's `L.head`**.

Across eras, `phi_strict_between_era_starts` gives a `+4` Φ-jump per
era. So the number of eras is `≤ (Φ - 6) / 4`. After that many eras,
Φ < 6, contradicting `phi_ge_init`.

### Plan in one paragraph

Given orbit-reachable `M([], 3, R)`, walk backward via γ.1/γ.2,
producing a chain of cursor-3 / cursor-5 configs along an
ever-lengthening D2-spine. By the per-era L-bound, the chain crosses
era boundaries every O(`L_head`) steps. Each era-crossing strictly
decreases an era-counting measure. So the chain is finite. But it has
no fixpoint — the cascade has no "init" landing — so it must
contradict `phi_ge_init`. ∎ (sketch)

---

## 2 · Definitions and invariants

These belong in a new file `era_orbit_d2spine.lean` (alternatively
extend `era_orbit_gamma.lean`).

### 2.1 D2-spine length

```lean
/-- Number of leading `2`s on L (used to measure D2-spine depth). -/
def listLeadingTwos : List Nat → Nat
  | 2 :: rest => 1 + listLeadingTwos rest
  | _ => 0

/-- D2-spine length of a config. Nonzero only for the canonical
    cursor-3 shape `M([2,...,2], 3, R)`. -/
def d2SpineLen : MacroConfig → Nat
  | .M L 3 _ => listLeadingTwos L
  | _        => 0
```

Properties to prove (≤ 30 lines each):

```lean
@[simp] theorem d2SpineLen_M_empty_3 (R) : d2SpineLen (.M [] 3 R) = 0
@[simp] theorem d2SpineLen_M_2cons_3 (L R) :
    d2SpineLen (.M (2::L) 3 R) = 1 + d2SpineLen (.M L 3 R)
theorem d2SpineLen_M_1cons_3 (L R) :
    L.head? ≠ some 2 → listLeadingTwos L = 0 →
    d2SpineLen (.M L 3 R) = 0
```

### 2.2 Cascade shape predicate

```lean
/-- `cfg` is on the cursor-3 D2-spine: `M([2,...,2], 3, R)`. -/
def OnD2Spine : MacroConfig → Prop
  | .M L 3 _ => ∀ x ∈ L, x = 2
  | _        => False

/-- `cfg` is at the D3-lifted layer: `M([1, 2,...,2], 5, R)`. -/
def OnD3Lift : MacroConfig → Prop
  | .M (1 :: L) 5 _ => ∀ x ∈ L, x = 2
  | _               => False
```

### 2.3 Era-witness map

The per-era bound needs an "era-start ancestor" assigned to each
config in the cascade. Rather than parameterising `IntraEraOf` along
the backward direction, lift the existing `IntraEra.exists_intraEraOf`
pointwise:

```lean
/-- Every orbit-reachable, non-`M0` cfg satisfies IntraEra; hence has
    a witnessing EraStartConfig. -/
theorem OrbitReachable.eraStart_witness {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hM : ∃ L c R, cfg = .M L c R) :
    ∃ e : EraStartConfig, IntraEraOf e cfg
```

This is **already provable** from existing infrastructure
(`IntraEra.exists_intraEraOf` + a lift from `OrbitReachable` to
`IntraEra` for non-M0 configs — note: `IntraEra` is broader than
"between two era-starts in the orbit", it just means "reached from
some era-start by sweep dynamics", which holds for any
orbit-reachable M-config).

If a clean lift is unavailable, fall back to:

```lean
def eraStartOf (cfg : MacroConfig) : Option EraStartConfig
  -- partial: returns Some when cfg is M-shape and a witness exists
```

with totality proved on demand.

---

## 3 · Phase decomposition

### Phase E.1 — Generalised D2/D3-spine predecessor characterisation (~80 L)

Generalise γ.2 to the n-th cascade layer:

```lean
/-- **E.1.a**: predecessor of `M([2,...,2 (n times)], 3, R)` for n ≥ 0
    is either:
      • `M([2,...,2 (n+1 times)], 3, d::R')` (D2 extension, k=19), or
      • `M([1, 2,...,2 (n-1 times if n ≥ 1)], 5, d::R')` (D3 lift, k=17).

    For n = 0 (i.e., `M([], 3, R)`), only the D2-extension branch is
    valid (D3 requires L_out non-empty in the predecessor reasoning;
    γ.1 forces it).  -/
theorem macroStep_M_2spine_3_predecessor_form
    {n : Nat} {R : List Nat} {cfg : MacroConfig} {k : Nat}
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (List.replicate n 2) 3 R)) :
    (∃ d R', cfg = .M (List.replicate (n+1) 2) 3 (d :: R') ∧
             R = 1 :: (d + 1) :: R' ∧ k = 19) ∨
    (n ≥ 1 ∧ ∃ L_tail d R',
       cfg = .M (1 :: List.replicate (n-1) 2) 5 (d :: R') ∧
       R = (d + 1) :: R' ∧ k = 17)
```

**Proof technique**: same `macroStep_eq_some_cases` 12-way split as
γ.1/γ.2; the `replicate n 2` form lets us subsume the special cases
n=0 (γ.1) and n=1 (γ.2) under one statement.

**E.1.b**: companion lemma for the D3-lift layer:

```lean
/-- Predecessor of `M(1 :: List.replicate n 2, 5, R)` is determined by
    the macroStep dispatch at cursor 5 with L head 1. The two
    productive cases are D5 (`sweep_left_empty` reverse) and D3 lift
    from cursor 7 (`sweep` with output cursor 5 means input cursor 3,
    impossible — must be cursor 7). -/
theorem macroStep_M_d3lift_5_predecessor_form
    {n : Nat} {R : List Nat} {cfg : MacroConfig} {k : Nat}
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (1 :: List.replicate n 2) 5 R)) :
    -- Several disjuncts characterising the predecessor.
    sorry
```

The exact disjunct list comes out of the case split; expect 1–3
productive cases (D5, possibly D11/zero_bounce with z=3 at this
specific shape).

---

### Phase E.2 — D2-spine bounded by era-start L within an era (~120 L)

The core structural fact:

```lean
/-- **E.2 (sweep-family preserves L-form)**: if `IntraEraOf e cfg` and
    `cfg = .M (List.replicate n 2) 3 R` then `n ≤ e.L.head?.getD 0 + 1`.

    Reason: sweep prefix from `M(L, c₀, [1])` → … → `M((L.head + i) :: L.tail,
    c₀ - 2i, [i+1])`. Sweep_and_shift fires when c reaches 3, with
    output L = L.tail (size shrinks by 1). The intra-era trajectory
    hits cursor-3 shapes only at end-of-sweep moments. After k
    sweep_and_shifts, L = (k-th tail of e.L), and the head equals 2
    iff the k-th tail starts with 2. -/
theorem IntraEraOf.d2SpineLen_bounded
    {e : EraStartConfig} {cfg : MacroConfig}
    (h : IntraEraOf e cfg) :
    d2SpineLen cfg ≤ e.L.length
```

The bound `e.L.length` is loose but suffices for cross-era recursion.
Tighter bound `e.L.head?.getD 0 + 1` works if needed but adds
arithmetic complexity.

**Proof structure** (induction on `IntraEraOf`):

| IntraEraOf constructor | d2SpineLen bound argument |
|---|---|
| `era_start` (cfg = e.toMacro, c ≥ 4 ≠ 3) | d2SpineLen = 0 ≤ e.L.length |
| `step` from cfg₀ via macroStep | case split on output cursor / shape; only output cursor 3 is interesting |

The interesting case is the inductive step landing at cursor 3. By
inversion of macroStep (γ.1 / γ.2 / E.1.a applied forward), the input
must be one of:
- D2: predecessor at cursor 3 with L = 2 :: L_in. `d2SpineLen` of
  predecessor is `1 + d2SpineLen(output)`. The IH gives the bound for
  the predecessor.
- sweep, sweep_and_shift, sweep_left_empty entering cursor 3: each
  reduces `|L|` by ≤ 1. Track via auxiliary lemma.

**Auxiliary lemma (E.2.a)** (≤ 40 L):

```lean
theorem macroStep_d2SpineLen_strict_decrease
    {cfg cfg' : MacroConfig} {k : Nat}
    (h : macroStep cfg = some (k, cfg'))
    (h_d2 : d2SpineLen cfg' ≥ 1) :
    -- Either the predecessor is a longer D2-spine, or `|L|` is
    -- larger by 1 in some compensating shape.
    d2SpineLen cfg + 1 = d2SpineLen cfg' ∨
    cfg.matches_some_non_d2_layer
```

This is the "L-conservation" property in disguise. Its statement
needs care: D2 grows the spine by 1 backward; D3 flips spine to D3-
lift; sweep / sweep_left_empty push without affecting cursor-3 spine.

---

### Phase E.3 — Cross-era recursion bound (~80 L)

Combine `phi_strict_between_era_starts` (Φ ≥ 6 + 4n at depth n) with
E.2 to bound the total cascade depth.

```lean
/-- **E.3**: there exists a Nat `N` such that any orbit-reachable
    `M([2^k], 3, R)` with `k ≥ N` is impossible.

    More precisely: for orbit-reachable `cfg = M([2^k], 3, R)`,
    `cfg.phi ≥ 6` (Φ-pruning) gives `R.sum ≥ 3 - 2k`, plus the
    era-witness `e` of `cfg` with `e.toMacro.phi ≥ 6 + 4·d` for
    `d` = era-depth, plus E.2 gives `k ≤ e.L.length`, plus the
    `e.L.length ≤ e.toMacro.phi - 4` structural bound. Combining:
    `k ≤ cfg.phi - 4 - 4·d_min`, but `d_min` grows with `k` because
    the cascade backward must traverse ≥ k-many era boundaries. -/
theorem cascade_depth_bounded {cfg : MacroConfig}
    (h : OrbitReachable cfg)
    {n : Nat} {R : List Nat}
    (hcfg : cfg = .M (List.replicate n 2) 3 R) :
    n ≤ (cfg.phi - 6) / 2 + cfg.phi    -- placeholder bound; refine
```

The exact inequality emerges from threading three facts:
1. cfg's era-start `e` has `e.L.length ≥ n` (from E.2).
2. `e.toMacro.phi ≥ 6 + 4 · d` where `d` = era-depth from init (from
   `phi_strict_between_era_starts`).
3. `e.toMacro.phi ≥ 1 + e.L.length` (since L_sum ≥ |L| + 1 for
   AllGe1 L with at least one entry ≥ 2, plus c ≥ 4 plus R.sum = 1).

Concrete numerical form to verify: if `n ≥ N₀`, then for any era-start
`e` with `e.L.length ≥ n`, `e.toMacro.phi ≥ 1 + n + 4 + 1 = n + 6`,
so `e.toMacro.phi - 6 ≥ n`. Coupled with γ.3.3 (`gammaFuel
non-decreasing`), the chain length contradicts the finite descent.

This phase is where the math has to be checked carefully. The key
inequality is whether the era's structural-Φ-lower-bound is large
enough to force a finite cascade.

**Tractability check** (do this BEFORE writing E.3 in full):
- Compute `e.toMacro.phi` for `e = M([2^k], c₀, [1])`: phi = 2k + c₀ + 1.
- For cfg at era-start, `e.L.length = k`, so phi ≥ 2·|e.L| + c_min + 1
  where c_min ≥ 4. ⇒ phi ≥ 2k + 5.
- Cascade backward through era-starts: each backward era-step decreases
  Φ by ≥ 4 (`phi_strict_between_era_starts` reverse direction).
  After n era-steps backward, `e_n.phi ≥ 6` forces `cfg.phi ≥ 6 + 4n`.
- Combined with `cfg = M([2^k], 3, R)` and `cfg.phi = 2k + 3 + R.sum`,
  the bound becomes `2k + 3 + R.sum ≥ 6 + 4n` where n is the era-depth.
- Need: `n ≤ |L|/2 + R.sum/4` or similar — the cascade depth is
  bounded by config size.

This is sketchier than ideal. **Check the math on paper / Python first.**

---

### Phase E.4 — Wire to `BadShape.base R` (~80 L)

Define a strong induction on cascade depth + config phi:

```lean
/-- **E.4**: for every `R`, `M([], 3, R)` is not orbit-reachable.

    Strong induction on a measure (cfg.phi, d2SpineLen cfg). At each
    layer n in the D2-spine cascade, applying γ.1 / γ.2 / E.1.a backward
    yields a predecessor whose measure is strictly smaller:
    - D2 backward: phi unchanged (sweep_and_shift Δ=0), but
      d2SpineLen + 1.  ← cascade DOES grow this measure.
    - D3 lift:    phi unchanged, d2SpineLen drops to 0, cursor → 5.
    - From cursor 5: sweep / sweep_left_empty paths phi-monotone or
      strict-positive M0 transitions.

    Termination via E.3: the cascade depth is bounded by O(phi). -/
theorem OrbitReachable.not_M_empty_3 {R : List Nat} :
    ¬ OrbitReachable (.M [] 3 R) := by
  -- Outer well-founded induction on cfg.phi (Nat).
  -- Inner case-split by γ.1 to identify D2 predecessor.
  -- Recurse on M([2], 3, _) via γ.2 (D2 OR D3 branches).
  -- D3 branch enters M([1], 5, _) territory: handle via separate
  -- lemma (E.4.a, see below).
  sorry

/-- **E.4.a**: cascade closure for the D3-lifted shape. -/
theorem OrbitReachable.not_M_d3lift {n : Nat} {R : List Nat} :
    ¬ OrbitReachable (.M (1 :: List.replicate n 2) 5 R)
```

**Proof skeleton** (the hard part):

```lean
theorem OrbitReachable.not_M_2spine_3 (n : Nat) (R : List Nat) :
    ¬ OrbitReachable (.M (List.replicate n 2) 3 R) := by
  -- Well-founded recursion on the lex pair
  --   (era-depth witness, n + spine_remaining).
  -- Or strong recursion on cfg.phi alone, which works because:
  -- - D2 backward: phi same, but the predecessor M([2^(n+1)], 3, _)
  --   has L-length n+1; by E.3 there's a phi-cap M such that for all
  --   n ≥ M, no orbit-reachable predecessor exists.
  -- - D3 backward: lifts to M([1, 2^(n-1)], 5, _); recurse via E.4.a.
  intro h_or
  -- ... outer induction skeleton ...
  sorry
```

The cleanest route is **two-level structural induction**:

1. **Outer**: induction on `n` (D2-spine length). Base case `n = N₀`
   (the cap from E.3) closed by phi-pruning. Inductive case: apply γ
   backward one D2 step, recurse.
2. **Inner**: when D3 branch fires, recurse via `not_M_d3lift`. The
   D3-lifted layer has its own well-founded measure (e.g.,
   `(d2SpineLen, cfg.phi)`).

A simpler but equivalent route uses **WellFoundedRecursion on Φ**
directly: if cfg is orbit-reachable, then phi ≥ 6 + 4·k for some
k ≤ n / 2 (E.3); pick the maximum such k and derive a contradiction
via the era-depth bound.

---

### Phase E.5 — Wire-up (Stage G analog) (~30 L)

Replace `sorry` in `era_orbit.lean:493` with `OrbitReachable.not_M_empty_3`:

```lean
theorem BadShape.not_OrbitReachable {cfg : MacroConfig}
    (h_bad : BadShape cfg) : ¬ OrbitReachable cfg := by
  induction h_bad with
  | base R =>
    intro h_or
    exact h_or.not_M_empty_3 R                    -- ← E.4 lands here
  | step h_bad' h_step ih =>
    intro h_or
    exact ih (h_or.step_macro h_step)
```

Then the existing `OrbitReachable.not_M_empty_3_full`
(`era_orbit.lean:506`) is closed automatically.

Two further `sorry`s in `era_orbit.lean` benefit:
- `era_shape_phi_strict_predecessor` step_R1 case (line 237).
- `phi_ge_init` step_R1 case (line 297).
- `not_M_1_5_1` step_R1 case (line 474).

These all become trivially closeable via mutual induction with
`not_M_empty_3` (the step_R1 predecessor is excluded by E.4 directly).

Finally, in `progress.lean:macro_progress` (line 58), replace
`exact reach_M_nil_3 hinv` with a contradiction derived from
`not_M_empty_3`. The OrbitReachable threading needs to be in place for
the dispatch (or accept that `macro_progress` operates on
`MacroInvariant` only and lift the result via the orbit-progress
wrapper at the call site in `progress.lean`'s `sweeper_never_halts`).

---

## 4 · Effort estimate

| Phase | Description | Lines | Difficulty | Risk |
|-------|-------------|-------|------------|------|
| E.1   | Generalised D2/D3 predecessor lemmas | 80 | medium | low |
| E.2   | D2-spine ≤ era-start `\|L\|` within era | 120 | medium-high | medium |
| E.3   | Cross-era cascade depth bound | 80 | high | medium-high |
| E.4   | Wire to `BadShape.base R` (well-founded recursion) | 80 | high | medium |
| E.5   | Wire-up + residual step_R1 cases | 30 | low | low |
| **Total** | | **~390 L** | medium-high overall | manageable |

Estimated calendar time: 2–4 days of focused work, assuming the
math-on-paper check at the start of E.3 confirms the bound. If the
bound fails (i.e., the era-depth argument doesn't actually constrain
cascade depth), the plan needs revision and time triples.

---

## 5 · Risks (in order of severity)

### R1 (high) · E.3 numerical bound may not close

The cross-era recursion claim "cascade depth ≤ O(phi) when cfg has
specific shape" relies on `e.toMacro.phi ≥ |e.L| + something` plus
`e.L.length ≥ d2SpineLen` plus iterated era-jumps. The precise
inequality may be off-by-one or require an additional invariant
(e.g., `e.L.sum` rather than `e.L.length` as the bound).

**Mitigation**: do the math-on-paper / Python-simulation check FIRST.
Concretely, enumerate eras for orbit-reachable era-starts at
phi ∈ {6, 10, 14, …, 30} and tabulate observed D2-spine lengths.
Verify the bound empirically before formalising.

**Fallback**: if the simple Φ-bound fails, use a 2-counter
well-founded measure `(era-depth, d2SpineLen)` with a non-Φ
relationship.

### R2 (medium-high) · IntraEraOf may not lift cleanly from OrbitReachable

E.2 needs `OrbitReachable cfg → IntraEraOf e cfg` for some `e`.
`IntraEra.exists_intraEraOf` exists but `OrbitReachable → IntraEra`
may have edge cases (M0-shape configs, configs reached only via
multi_bounce/R2/R3 constructors that bypass macroStep).

**Mitigation**: pre-check by reading `era.lean`'s `IntraEra` definition
(line 282) and verify all OrbitReachable constructors land in a
config that's reachable from some era-start via macroStep alone.
If not, restrict E.2 to the macroStep-reachable subset and handle
non-macroStep constructors (R2/R3 outputs) separately.

**Fallback**: define a weaker era-witness predicate that holds for all
orbit-reachable M-configs without going through `IntraEra`. The witness
just needs to bound `|L|` from above.

### R3 (medium) · Well-founded recursion infrastructure

E.4's well-founded recursion on a lex pair / Nat measure is doable in
Lean 4 / Mathlib but adds friction. Threading `decreasing_by` through
12+ OrbitReachable cases (per the analysis in
`plan-era-graded-not_R1.md` Sub-plan C) is repetitive.

**Mitigation**: encapsulate the recursion in a single
`Nat.strongRecOn` invocation on cfg.phi (or a helper measure). The
inner case-split on OrbitReachable doesn't need its own well-founded
recursion; it folds into the strong-induction step.

### R4 (medium) · D3-lift cascade not yet bounded

Phase E.4.a (`not_M_d3lift`) is sketched but not detailed.
`M([1, 2^(n-1)], 5, R)` has its own backward predecessors via D5
(sweep_left_empty backward) and possibly D11 (zero_bounce reverse at
specific R values).

**Mitigation**: extend Phase E.1 with a third generalisation:

```lean
theorem macroStep_M_d3lift_predecessor_form ...
```

mirroring E.1.a/b for the D3-lift family. The two-shape cascade
becomes a four-shape cascade if M0 enters; bound them all under one
induction.

### R5 (low) · Residual step_R1 cases mutual induction

E.5 closes `step_R1` cases via mutual induction. Lean 4's
mutual-induction support is solid but requires careful theorem
ordering. The current `era_orbit.lean` has three `step_R1` sorries
that all become discharged once `not_M_empty_3` is in scope.

**Mitigation**: prove `not_M_empty_3` standalone (without depending
on the three downstream sorries), then refactor those theorems to
discharge their step_R1 cases via `not_M_empty_3`.

---

## 6 · Concrete next steps (dependency order)

### Step 1 — math-on-paper check (1 hour)

Before writing any Lean: confirm the era-depth bound algebraically.

- Take `e = M([2^k], 5, [1])` for k = 1, 2, 3.
- Compute Φ(e) = 2k + 6.
- Compute era-depth from init (init.phi = 6, jumps ≥ +4 per era-step).
- Verify: `era-depth(e) ≥ k/2` or similar.
- If yes, E.3 has a chance. If no, identify the shape that breaks the
  bound and revise.

**Cross-reference**: era-sim's 63 K era-boundary dataset
(`era_full.jsonl`) — query for occurrences of L = `[2^k]` at era-start
and tabulate (Φ, k) pairs.

### Step 2 — implement E.1.a (generalised γ.2)

File: `era_orbit_d2spine.lean` (new), import `era_orbit_gamma`.

Lemma: `macroStep_M_2spine_3_predecessor_form` (signature in §3).

Proof: same 12-way case split as γ.1/γ.2 with `replicate n 2` shape.
Subsumes γ.1 (n = 0) and γ.2 (n = 1) as special cases.

### Step 3 — implement E.2 (sweep-family L-bound)

Lemma: `IntraEraOf.d2SpineLen_bounded`.

This is the *technical core* of the plan. Outline:
- Induction on `IntraEraOf e cfg`.
- `era_start`: cfg has cursor ≥ 4, so `d2SpineLen cfg = 0`. Bound holds.
- `step`: case split on macroStep dispatch.
  - sweep / sweep_left_empty: cursor moves by ±2; if output is cursor 3,
    the input must be cursor 5 with L head 1 (sweep) or L = [] (left_empty).
    Either way `d2SpineLen` of input is 0; output `d2SpineLen` is 0
    or 1 (depending on residual L).
  - sweep_and_shift: input cursor 3, output cursor `a + 1`; output L is
    input L with head removed.

Auxiliary lemma E.2.a (`macroStep_d2SpineLen_strict_decrease`) packages
the shape-by-shape arithmetic.

### Step 4 — formalise E.3

Define `cascade_phi_bound` as the max D2-spine length compatible with
`OrbitReachable` at given Φ. Prove via E.2 + `phi_strict_between_era_starts`.

If math check (Step 1) reveals a tighter bound is needed, defer to a
non-Φ measure (e.g., `(era-depth, d2SpineLen)` lex).

### Step 5 — close E.4

Use strong induction on the chosen measure. Apply γ.1 (base) and
E.1.a (inductive D2 / D3 branch) to descend.

D3 branch handled by `not_M_d3lift` (E.4.a) — recursive call with
strictly smaller measure.

### Step 6 — discharge residual sorries (E.5)

Replace `sorry` at:
- `era_orbit.lean:493` (`BadShape.not_OrbitReachable.base R`).
- `era_orbit.lean:237` (`era_shape_phi_strict_predecessor` step_R1).
- `era_orbit.lean:297` (`phi_ge_init` step_R1).
- `era_orbit.lean:474` (`not_M_1_5_1` step_R1).
- `progress.lean:58` (R1 axiom invocation).

Each requires only a one-liner: discharge via `OrbitReachable.not_M_empty_3`.

### Step 7 — verify axiom hygiene

After build: `#print axioms Sweeper.sweeper_never_halts`.

Expected:
```
{propext, Classical.choice, Quot.sound,
 reach_multi_bounce_last_2_long, reach_multi_bounce_last_2_mid_1}
```

R1 (`reach_M_nil_3`) should be **gone**.

---

## 7 · Files touched

| File | Modification |
|------|--------------|
| `era_orbit_d2spine.lean` (new, ~300 L) | Phases E.1–E.4: definitions + theorems |
| `era_orbit.lean` | Phase E.5: discharge 4 sorries |
| `progress.lean` | Phase E.5: replace R1 axiom invocation |
| `lakefile.toml` | Add `era_orbit_d2spine` to Sweeper roots |
| `FILES.md` | Index new file |
| `LOG.md` | Log E completion + axiom-set update |

---

## 8 · Cross-references

### Used inputs

- `era_orbit_gamma.lean:macroStep_M_empty_3_predecessor_form` (γ.1) — base case.
- `era_orbit_gamma.lean:macroStep_M_2list_3_predecessor_form` (γ.2) — n=1 special case.
- `era_orbit_gamma.lean:gammaFuel_macroStep_nondec` (γ.3.3) — Φ non-decrease.
- `era.lean:EraStartConfig`, `IntraEra`, `IntraEraOf` — era-graded structure.
- `era.lean:macroStep_M_intra_era_preserves_L_ne_nil` — sweep family preserves L ≠ [].
- `era.lean:sweep_iter_M_cons_output` — explicit n-sweep iteration form.
- `phi_era.lean:phi_strict_across_era_step` — +4 Φ-jump per era-step.
- `phi_era.lean:phi_strict_between_era_starts` — same, in orbital form.
- `era_orbit.lean:OrbitReachable.phi_ge_init` — Φ ≥ 6 lower bound.
- `era_orbit.lean:OrbitReachable.not_phi_lt_six` — Φ-pruning corollary.

### Closes

- `era_orbit.lean:493` (`BadShape.base R` cascade closure).
- `era_orbit.lean:506` (`OrbitReachable.not_M_empty_3_full`) — automatic.
- `era_orbit.lean:237` (step_R1 in `era_shape_phi_strict_predecessor`) — via mutual induction.
- `era_orbit.lean:297` (step_R1 in `phi_ge_init`) — via mutual induction.
- `era_orbit.lean:474` (step_R1 in `not_M_1_5_1`) — via mutual induction.
- `progress.lean:58` R1 axiom invocation.

### Supersedes

- `plan-era-graded-not_R1.md` Sub-plans A1, A2, B, C, D, F, G — all
  rolled into the unified E pipeline.
- `plan-era-graded-not_R1.md` Option C-3 — Sub-plan E IS its
  formalisation post-γ.

---

## 9 · Decision criteria (when to pivot)

Pivot away from Sub-plan E to strictly-decreasing
measure (Path 1) IF:

1. **Math-on-paper check (Step 1) fails** — the era-depth bound
   doesn't actually constrain cascade depth. → revisit Path 1 with
   a non-parity measure (e.g., a Diophantine quantity that decreases
   along D2-spine + D3-lift transitions).
**Fallback**: if the simple Φ-bound fails, use a 2-counter
well-founded measure `(era-depth, d2SpineLen)` with a non-Φ
relationship.

2. **E.2 proof exceeds 200 lines** — the IntraEraOf induction has
   more cases than expected. → split E.2 into several lemmas; if
   still over budget, switch to
**Fallback**: define a weaker era-witness predicate that holds for all
orbit-reachable M-configs without going through `IntraEra`. The witness
just needs to bound `|L|` from above.

3. **E.3 well-founded measure invalid** — multiple eras don't
   strictly decrease the measure. → introduce a hybrid measure or
   pivot to a non-era-graded approach (e.g., direct Φ-pruning with
   a refined lower bound on `M([2^k], 3, R)`).

If none of these triggers fire by the end of Step 4, commit to the
plan through E.5.

---

## 10 · Comparison to the alternative paths

| Path | Status | Estimated effort | Risk |
|------|--------|------------------|------|
| **E (this plan)** | active | 2–4 days, ~390 L | medium-high (E.3 numerical bound) |
| Path 1 (parity / strict measure) | scouted, insufficient standalone | would need to recreate Path 2's work | high (no standalone closure exists) |
| Path 3 (F2 black-box) | blocked on F2 conjecture | small (≤ 50 L) once F2 lands | depends on F2 being closed elsewhere |

Sub-plan E is the only path with **both** structural finiteness AND a
formalisable Lean recursion. Recommend committing to it.
