# TODO: canonical_progress (IN PROGRESS)

## Status (2026-04-18)

Refactored invariant from predicate `ValidDigits` to inductive
`ReachableShape` with 6 constructors (init, via_R1..R6). `canonical_progress`
reduced to `ReachableShape.progress_step`. Now 4/6 cases fully closed and
2/6 cases partially closed; 2 sub-sorries remain, both sharing the same
missing piece (tail traversal for leading-odd shapes).

### Closed cases
- **init**: apply R4 on `[1, 1]`.
- **via_R3/R4/R5**: output has leading `2n` (even); dispatch on `n = 0 ?`
  (apply R1) or `n ≥ 1` (apply R6).
- **via_R1 / `a` odd**: `a + 3 = 2(k+1) + 2` is positive even → R6.
- **via_R6 / `a` even**: `a + 1 = 2k + 1` is odd, so shape is `(2n+1) :: (2k+1) :: rest`
  → R4 (rest = []) or R5 (rest nonempty).

### Remaining (4 sub-sorries, 2 kinds)

Both via_R1 a-even and via_R6 a-odd cases split by structure of their
remaining tail; the singleton / cons-cons-b-odd leaves are closed. What
remains:

**Kind A — halt-configuration unreachability (2 sorries):**
- via_R1 a-even / rest=[0]: xs = [2(k+1)+1, 0]
- via_R6 a-odd / rest=[0]: xs = [2n+1, 2k+2, 0]

Attempted 2026-04-18: tried to prove `¬ ReachableShape [c, d] for c ≥ 2`
as an intermediate invariant by induction. **This is FALSE** — e.g.
`[4, 1]` is ReachableShape (via R1 from `[0, 1, 1]` ← R4 from `[1, 1]`).

Discovery: length-2 reachable shapes form an infinite family: `[1, 1]`,
`[4, 1]`, `[3, 2]`, `[5, 2]`, `[6, 1]`, ... The real invariant is NOT
"no length-2 with leading ≥ 2" but rather "no halt-shape is reached".
A halt-shape is `(2n+1) :: middle ++ [0]` with `AllPosEven middle`.

Naïve attempt `∀ xs, ReachableShape xs → ¬ IsHalt xs` also fails under
direct induction: via_R1 doesn't preserve a simple halt-negation because
the sub-shape `0 :: a :: rest` has leading 0 (trivially not halt), and
the output `(a+3) :: rest` may become halt-shaped through new structure.
A stronger induction invariant tracking AllPosEven-structure across the
full ancestry is needed.

**Kind B — deep tail traversal (2 sorries):**
- via_R1 a-even / rest=b::c::rest'' with b even
- via_R6 a-odd / rest=b::c::rest'' with b even

These need a classifier that walks through positive-even digits to find
either (i) the first odd digit (→ R5), (ii) the list end with odd last
(→ R4), (iii) the list end with positive even last (→ R3), or (iv) a
halt-shape (excluded). The tail's structure isn't available from the
local context — it must be extracted from `h_sub` via constructor
inversion, sharing the Kind A difficulty.

### Root cause for all 4 remaining sub-sorries

All four sub-sorries share a single underlying obstacle: extracting
detailed structural information about intermediate list segments from
the `ReachableShape` ancestry. A direct induction on `ReachableShape`
does not preserve the needed invariants (as demonstrated by the false
`not_len2_lead_even` attempt). The proof likely requires:

1. **Explicit structural classification proved mutually with `ReachableShape`**
   — redefine the inductive with built-in classifier labels, OR
2. **A strong lexicographic / measure-based argument** using the fact
   that each rule strictly grows the potential (e.g., sum of digits) —
   bounds on what shapes can appear at each "growth level".

Either direction is ~200-400 lines of careful proof engineering.

### Closed (as of 2026-04-18)
- init, via_R3/R4/R5 fully.
- via_R1 a-odd fully; via_R1 a-even rest=[b]/b-odd + rest=[b]/b-pos-even
  + rest=cons-cons/b-odd.
- via_R6 a-even fully; via_R6 a-odd rest=nil + rest=[b]/b-odd +
  rest=[b]/b-pos-even + rest=cons-cons/b-odd.

## Goal

```lean
theorem canonical_progress :
    ∀ c, IsCanonical c →
      ∃ k, 0 < k ∧ IsCanonical (tmRun c k) ∧ (tmRun c k).state ≠ none
```

where `IsCanonical c := ∃ xs, c = MacroConfig xs ∧ ValidDigits xs`.

## The invariant design problem

The current `ValidDigits` is too weak:

```lean
def ValidDigits (xs : List Nat) : Prop :=
  2 ≤ xs.length ∧
  (∀ n middle, xs = (2*n+1) :: middle ++ [0] → ¬ AllEven middle)
```

Issues:
1. Allows `[0, a]` (length 2, leading 0). But R1 applied gives `[a+3]` — length 1, BREAKS invariant.
2. Allows `[0, 0]`. No rule applies cleanly (length 2 with leading 0).
3. R3/R4 now require `AllPosEven middle` (positive even middle digits), which ValidDigits doesn't guarantee.
4. Doesn't uniquely determine which rule applies.

## Strengthened invariant (proposal)

```lean
def ValidDigits (xs : List Nat) : Prop :=
  2 ≤ xs.length
  ∧ (xs.head? = some 0 → 3 ≤ xs.length)              -- leading 0 → length ≥ 3
  ∧ (∀ n middle, xs = (2*n+1) :: middle ++ [0] →
       ¬ AllEven middle)                              -- R2 exclusion
  ∧ (∀ n middle last, xs = (2*n+1) :: middle ++ [last] ∧ last ≠ 0 ∧ AllEven middle →
       AllPosEven middle)                             -- AllPosEven when R3/R4 applies
  ∧ (∀ n middle m x rest,
       xs = (2*n+1) :: middle ++ (2*m+1) :: x :: rest ∧ AllEven middle →
       AllPosEven middle)                             -- AllPosEven when R5 applies
```

## Required preservation proofs

For each rule, show ValidDigits is preserved:

### R1: `[0, a, rest] → [(a+3), rest]`
- Input length ≥ 3 (by strengthened invariant).
- Output length = input length - 1 ≥ 2. ✓
- Output's leading digit `a+3 ≥ 3`, so leading-0 clause vacuous.
- R2-exclusion: if output = `(2n+1) :: m ++ [0]`, then input = `0 :: (2n+1) :: m ++ [0]`. Input was `0 :: a :: rest` so `a = 2n+1` and `rest = m ++ [0]`. Input's R2-clause (with different n', middle'): `0 :: a :: rest = (2n'+1) :: m' ++ [0]` would need `0 = 2n'+1`, impossible. So input's clause is vacuously true. Need to derive output's clause independently.

### R3: `[(2n+1), middle, (2m+2)] → [(2n), middle, (2m+2), 0]`
- Input has AllPosEven middle (from strengthened invariant).
- Output length = input length + 1.
- Output leading = 2n. If n=0, leading is 0 AND length ≥ 3 (OK).
- R2-exclusion: output ends in 0. If output = `(2n'+1) :: m' ++ [0]`, then `2n = 2n'+1` — impossible (even ≠ odd). So vacuously true.

### R4: `[(2n+1), middle, (2m+1)] → [(2n), middle, (2m+1), 1]`
- Output ends in 1, not 0. R2-exclusion vacuously true.
- Leading 2n, even. If n=0 (leading 0), length ≥ 3.

### R5: `[(2n+1), middle, (2m+1), x, rest] → [(2n), middle, (2m+1), x+1, rest]`
- Output ends in rest's last element.
- If rest ends in 0: output matches R2-pattern `(2n') :: ... ++ [0]` only if 2n = 2n'+1 (impossible).
- **But wait**: output starts with 2n (even). The R2-pattern needs leading odd. So vacuously OK.

### R6: `[(2n+2), a, rest] → [(2n+1), a+1, rest]`
- Output leading = 2n+1 (odd). Not leading 0.
- If rest = [0] (so output = [2n+1, a+1, 0]):
  - Output matches R2: middle = [a+1], last = 0. Need ¬AllEven [a+1], i.e., ¬Even (a+1).
  - Input: `[2n+2, a, 0]`. Was this reachable? Input is R6-input: middle = [a], last = 0.
    - From input's R2-exclusion (strengthened): ¬ AllEven [a]? Hmm, but input starts with even (2n+2), not odd. So R2-exclusion is vacuously true for input.
  - So we need another way to derive `¬Even (a+1)`, i.e., `Odd (a+1)`, i.e., `Even a`.
  - **This is the key preservation obligation for R6**: if `[2n+2, a, 0]` satisfies ValidDigits,
    then `a` must be even (so that `a+1` is odd, preserving R2-exclusion).
  - Need an additional invariant clause: when leading is positive even and last is 0,
    the middle digits (which is just [a] here) are all odd. Hmm, that's different from AllPosEven.

This suggests the invariant needs yet another clause.

## Simpler approach: recursive reachability

Define IsCanonical inductively as "reachable from [1, 1] via macro rules":

```lean
inductive ReachableShape : List Nat → Prop
  | init : ReachableShape [1, 1]
  | via_R1 (a : Nat) (rest : List Nat) :
      ReachableShape (0 :: a :: rest) → rest ≠ [] →
      ReachableShape ((a+3) :: rest)
  | via_R3 ... | via_R4 ... | via_R5 ... | via_R6 ...
```

Then `canonical_progress` becomes: for any ReachableShape xs, some rule applies and the result is also a ReachableShape.

This sidesteps the invariant-design problem but shifts work to:
1. Proving [1, 1] is reached initially (reaches_canonical).
2. Showing each shape admits a rule application (case analysis).
3. Showing the resulting shape is also ReachableShape (by construction).

## Recommended approach

Given the complexity, I recommend:

1. **Step A**: Add inductive ReachableShape + define IsCanonical via it.
2. **Step B**: Prove by case analysis that every ReachableShape xs has some rule that applies. Each "rule applies" gives a specific k, new xs', and ReachableShape xs'.
3. **Step C**: Package into canonical_progress.

Estimated scope: ~150-200 lines.

## Alternative: accept the gap

`nonhalt` uses `canonical_progress` via `nonhalt_of_progress`. If canonical_progress
has a sorry, the overall nonhalt theorem is gated on this one sorry. Since all
5 macro rules are proved, the gap is purely about invariant maintenance — a
proof-engineering issue, not a mathematical one.

Current state: 1 sorry in the entire file (canonical_progress).
