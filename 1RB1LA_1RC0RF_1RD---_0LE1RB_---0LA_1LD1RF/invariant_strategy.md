# Strengthened-invariant strategies

A taxonomy of "stronger statements" available beyond the existing
`MacroInvariant`. Each item is a *form* of claim — the same semantic content
can often be expressed in multiple forms, and the form determines how the
proof gets written in Lean.

Companion to `TACTIC_PLAN.md`. Relevant for closing the remaining R1 axiom
and/or pursuing Option 2 (algebraic/2-adic invariant) from that file.

## Context

`MacroInvariant` is purely a **local structural** property:

```lean
def MacroInvariant : MacroConfig → Prop
  | .M L c R => AllGe1 L ∧ c ≥ 2 ∧ AllGe1 R ∧ R ≠ []
  | .M0 L R => AllGe1 L ∧ AllGe1 R ∧ L ≠ [] ∧ R ≠ [] ∧ NoHaltPattern R
```

Every clause is a fact about a single configuration. It says nothing
about: list lengths, sums, era count, cursor growth, or any relation
between successive configurations.

This is enough to make the dispatch in `macro_progress` total (every
shape gets handled) but it is not enough to *exclude* the shapes that
empirically never appear. Closing those axioms — or proving non-halting
without depending on them — requires an additional, stronger statement.

Below is the taxonomy of forms that statement could take.

## A. Per-configuration invariants (extend `MacroInvariant`)

A predicate `I : MacroConfig → Prop` that holds at the initial state and
is preserved by every macro/raw transition.

1. **Numeric lower bounds** — `cursor ≥ f(...)`, `|L| ≥ g(...)`,
   `sum L ≥ h(...)`. Witness for non-halting via unboundedness; useful
   for excluding small shapes (e.g. R1 wants `|L| ≥ 1` whenever
   `cursor = 3`).
2. **Numeric equalities** — `cursor + 2 · sum L = const`,
   `cursor mod 4 = some_constant`, etc. The 2-adic / Mersenne-style
   claims sit here.
3. **Structural exclusions** — "if `cursor = 3` then `L ≠ []`",
   "L never has 1 in interior", "R's last is always 2 when cursor is 0".
   Directly closes R1/R3-style axioms.
4. **List-shape patterns** — "L has the form `[a₁, a₂, …, aₙ]` with
   `a₁ > a₂ > … > aₙ ≥ 1`" (descending run lengths, observed
   empirically). Pattern-match on shape rather than numeric content.
5. **Conjunction of any of the above** — multi-clause invariant, common
   in Mxdys/Pillai-style proofs.

## B. Pair-relational (potential) invariants

A function `Φ : MacroConfig → ℕ` (or any well-ordered type) compared
between successive configurations.

1. **Strictly increasing potential** `Φ(cfg') > Φ(cfg)` on every
   transition — proves the orbit visits unboundedly many distinct
   configs, which combined with finite-config-per-Φ-value gives
   non-halting.
2. **Non-decreasing with periodic strict increase** — Φ doesn't grow
   on every step, but does grow at each era boundary; same conclusion
   at coarser granularity.
3. **Bounded-difference Φ** — `|Φ(cfg') − Φ(cfg)| ≤ k(cfg)`; useful for
   bookkeeping but rarely enough on its own.
4. **Multi-component lex-Φ** — `(Φ₁, Φ₂)` with lexicographic comparison;
   can encode "era count, then within-era progress".

## C. Era-indexed claims

Statements about the state observed *at era boundaries* — i.e., the
discrete-time system `cfg_n = state at end of era n`.

1. **Closed-form L_n** — `L_n = f(n)` for explicit `f` (e.g.,
   `L_n[k] = some recursion`). Strongest possible; equivalent to "we
   know everything".
2. **Recurrence** `cfg_{n+1} = T(cfg_n)` for a specific finite-step
   `T`; reduces non-halting to non-halting of `T`'s iteration.
3. **Era-monotonicity** — some scalar `ψ(cfg_n)` is monotone in `n`
   (length of L grows, cursor grows, sum grows). Weaker than recurrence;
   might be enough.
4. **Era-modular** — `ψ(cfg_n) ≡ const (mod p)` for some `p`. The
   2-adic / Collatz-style invariant family.
5. **Eventually-stable shape** — beyond some era N, `cfg_n` has a fixed
   shape (e.g., `M([·, …, 1], c, [1])` always). Lets you reason about
   a much smaller set after era N.

## D. Algebraic / number-theoretic structure

Targeting closed-form computability rather than just preservation.

1. **2-adic invariant** — embed `cfg` into ℤ₂ (interpret L as 2-adic
   digits), prove the orbit corresponds to a 2-adic odometer / known
   transformation.
2. **Polynomial / generating-function identity** — `∑ aₖ xᵏ` (with
   `L = (a₁, a₂, …)`) satisfies `f_{n+1}(x) = R(x) · f_n(x) + s(x)`.
3. **Linear recurrence over Q or Z** — components of L satisfy a
   fixed-coefficient linear recurrence.
4. **Collatz-like dynamical reduction** — show the era map is conjugate
   to a known Collatz-like iteration on ℕ; cite (or prove) non-halting
   of that iteration.
5. **Continued-fraction / Euclidean algorithm structure** — common in
   TMs that simulate gcd.

## E. Set-theoretic / reachability invariants

Move to an inductively-defined subset of macro configs.

1. **Inductive reachable set** — `Reach` defined as "init + closed
   under transitions"; prove `Reach ⊆ NonHalting`. (`OrbitReachable` is
   exactly this; the cascade in `phase2.lean` adds the "exclude bad
   shapes" half.)
2. **Co-inductive non-halting set** — largest set `N` with
   `cfg ∈ N → step(cfg) ∈ N ∧ cfg.state ≠ none`. Prove init ∈ N.
   Symmetric formulation; useful when you can describe the *closed* set
   easily.
3. **Reachability negations** — for each known-bad shape `B`,
   `Reach cfg → cfg ≠ B`. Closes axioms one at a time. (Plan A for R1.)
4. **Closure under regular operations** — `Reach` characterized as the
   language accepted by some finite automaton on the L sequence.
   Verifiable by inclusion check.

## F. Bisimulation / morphism to a simpler system

A map `φ : MacroConfig → S'` to a smaller system, with
`φ(step(cfg)) = step'(φ(cfg))`.

1. **Forgetful projection** — collapse to "era number" or "L's first
   element"; prove the projection is non-halting.
2. **Quotient by symmetry** — identify configs that differ only by
   some symmetry, work modulo that.
3. **Interpretation as another known TM** — show the macro dynamics
   equals the dynamics of a previously-proved-non-halting TM.
4. **Embedding into infinite-state automaton** — like a counter machine
   or pushdown automaton with known liveness properties.

## Choosing content

For each form there's a separate "what content?" decision: which of

- `cursor`
- `|L|`, `|R|`
- `sum L`, `sum R`
- `head L`, `last L`, `head R`
- `sum L mod 2^k`
- `era count`
- `|L| − cursor`, `cursor + sum L`, etc.

is the relevant quantity. The form (A–F) tells you *how* to write the
claim; the content tells you *what specifically* it claims.

## Recommendations

- For closing **R1** (the remaining axiom), the cheapest viable forms
  are A.3 (structural exclusion, "if cursor = 3 then L ≠ []") and E.3
  (reachability negation, the cascade in `phase2.lean`).
- For an empirically-driven Option 2, the most realistic forms are
  C.2 (era recurrence) and D.1 (2-adic invariant) — these match the
  kinds of invariants found for related sweeping TMs (LucysMoonlight,
  Pillai/ValidS).
- For a bulletproof non-halting proof that doesn't depend on R1 at all,
  the cleanest is B.1 (a strict potential) — but no obvious candidate
  `Φ` has yet been found for this TM.

## Empirical-data constraint

`L` data points are scarce: only ~221 eras occur in the first 1 billion
raw TM steps, ~600–800 in the 51 B prior runs. Fitting a recurrence
that depends on more than ~50 prior eras is not realistic at this
sample size. Any Option-C/D candidate should be guessable from
low-order eras (where the L stack is short) or be derivable from
structural reasoning rather than purely from data.
