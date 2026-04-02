# Proof Progress Report: 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

## Summary

- **Total theorems**: 13 (4 shift/transition, 9 conjectured)
- **Proven**: 9 (4 shift/transition + 5 conjectured)
- **Remaining sorry**: 4
- **1 theorem has wrong statement** (`sweep_left_zero_shift`)

---

## Proven Theorems

### `A_shift` / `F_shift` (identity sweeps)
Proven by induction on k using `tm_ind_succ`. Standard shift lemma pattern.

### `bcd_extension`
Proven by `sw_steps`. States that B at right edge with `ones (k+1)` to
the left and `zeros (p+2)` to the right reaches state A in 5 steps
with `true :: false :: false :: zeros p` on the right.

### `f_bounce_interior`
Proven by `sw_steps`. States that F reading 0 with `ones (k+1)` to
the left bounces back as F in 3 steps, with a new zero-marker prepended
to the left tape. Requires `k+1 ≥ 1` so D sees a 1 (not 0).

### `sweeper_init_to_era0`
Proven by `rfl`. The machine reaches `E_Config 4 0` (all-1s tape of
length 5, state D at rightmost cell) after exactly 19 steps.

### `era_0_to_1`
Proven by `rfl`. From `E_Config 4 0` to `E_Config 10 0` (all-1s tape
of length 11) in exactly 65 steps.

---

## Remaining Sorries

### 1. `sweep_left_zero_shift` (line 180) — **STATEMENT IS WRONG**

**Current statement**: Starting from state A reading 1, with a
zero-marker at distance `a` on the left and arbitrary `R` on the right,
after some steps we reach state A reading 1 with the zero moved to
the right side.

**Why it's wrong**: After A sweeps left to the zero (a+1 steps via
`A_shift`), then A,0→1RB and B,1→0RF, we end up in **state F going
right**, not state A. Getting back to state A requires F to traverse
the entire right side of the tape, hit the right edge, BCD extend,
E→A bounce — a full sweep cycle. The resulting tape would also have
extra content from BCD extension, not just `[false] ++ R ++ zeros p`.

**The correct decomposition** is a sequence of smaller lemmas:

1. **A-sweep-to-zero**: A reading 1 with `ones a ++ [false] ++ L`
   on the left sweeps left in `a+1` steps to reach A reading 0.
   (Already captured by `A_shift`.)

2. **A-bounce-to-F**: A reading 0 → 1RB, then B reading 1 → 0RF.
   Two concrete steps producing state F with a new zero-marker on
   the left. (2 steps, provable by `sw_steps`.)

3. **F-sweep-through-ones**: F sweeps right through `ones n` to the
   next cell. (Already captured by `F_shift`.)

4. **Full sweep cycle**: Composing all phases including F-bounces at
   interior zeros and BCD extension at the right edge. This would need
   a specific tape shape (e.g., `ones a` with exactly `m` interior
   zeros at known positions) to state precisely.

**Obstacle**: The "zero-marker moves inward" property is an emergent
behavior of the full sweep cycle, not a single step. Formalizing it
requires specifying the exact tape structure (positions of all
zero-markers) and tracking how each one moves. This is the core
inductive argument and is nontrivial.

### 2. `c1_never_reached` (line 156) — **HARD: GLOBAL INVARIANT**

**Statement**: For all k, either the machine after k steps is not in
state C, or the head reads 0 (false).

**Why it's hard**: This is a global reachability invariant. C is only
entered via B,0→1RC, and B reads 0 only at the right tape edge. The
next cell (what C reads) is also 0. But proving this requires showing
that B *never* reads 0 at an interior position — equivalently, that
the zero-markers in the tape are never in the position directly under
the head when the machine is in state B.

**Mathematical obstacle**: Needs a comprehensive **tape invariant**
characterizing all reachable configurations:

```
  0^∞  1^a₁  0  1^a₂  0  ...  1^aₖ  [HEAD in region]  ...  0^∞
```

Specifically, it must capture:
- The relationship between the head position and zero-marker positions
- Which states appear at which head positions
- That B is only ever at positions right of all written tape content

This invariant must be:
1. Satisfied by the initial configuration
2. Preserved by every transition step (6 states × 2 symbols = 12 cases,
   minus 2 undefined = 10 cases to check)

**Proof strategy**: Define a predicate `IsReachable : Config 6 → Prop`
capturing the tape structure. Prove `IsReachable (initConfig 6)` and
`∀ c, IsReachable c → IsReachable (step sweeper c)`. Then derive
`c1_never_reached` as a corollary.

**Key difficulty**: Defining `IsReachable` correctly. The tape structure
is complex: the number and positions of zero-markers change each sweep
cycle, and the head moves through different phases (A sweep left, F
sweep right, BCD extension). A single invariant must encompass all
these phases simultaneously.

### 3. `e0_never_reached` (line 163) — **HARD: GLOBAL INVARIANT**

**Statement**: For all k, either the machine is not in state E, or the
head reads 1 (true).

**Same obstacle as c1**: E is only entered from D,0→0LE, and D reads 0
only at the right tape edge. The cell one step left is always a 1
(the rightmost written cell). Proving this formally requires the same
tape invariant as `c1_never_reached`.

**In fact**, c1 and e0 share the same invariant and should be proved
together. The invariant says:
- B reads 0 only at position `max_tape + 1` (one beyond the rightmost
  written cell)
- D reads 0 only at position `max_tape + 1`
- Therefore C (entered from B,0) always reads 0 (at `max_tape + 2`)
- Therefore E (entered from D,0) always reads 1 (at `max_tape`)

### 4. `sweeper_never_halts` (line 274) — **HARD: MAIN THEOREM**

**Statement**: For all k, `(run sweeper (initConfig 6) k).state ≠ none`.

**Dependency**: This follows directly from `c1_never_reached` and
`e0_never_reached`. The only undefined transitions are C,1 and E,0.
If we can show neither is ever reached, the machine never halts.

**Proof sketch** (assuming c1 and e0 are proved):
```lean
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  induction k with
  | zero => simp [run, initConfig]
  | succ k ih =>
    -- Need: step sweeper (run sweeper (initConfig 6) k) has state ≠ none
    -- The only way state becomes none is C,1 or E,0
    -- By c1_never_reached and e0_never_reached, these never happen
    sorry
```

The induction step requires knowing that `step sweeper c` produces
`state = none` iff `c` is in state C reading 1 or state E reading 0.
Combined with c1 and e0, this gives the result.

---

## Recommended Next Steps

1. **Fix `sweep_left_zero_shift`**: Replace with smaller, correct lemmas
   for each phase of the sweep cycle. The A-bounce-to-F step (2 concrete
   steps) is trivially provable. The full sweep cycle lemma needs
   specific tape structure.

2. **Define `IsReachable`**: This is the core challenge. A possible
   approach:
   - Define tape regions: "left zone" (ones with zero-markers, left of
     head), "right zone" (ones with zero-markers, right of head),
     "blank zone" (all zeros beyond the tape)
   - Specify which states can appear in which zone
   - Show the invariant is preserved by `step`

3. **Prove c1 + e0 together**: They share the same invariant.

4. **Derive `sweeper_never_halts`**: Should be straightforward once
   c1 and e0 are proved.

**Estimated difficulty**:
- Step 1: Easy (a few hours)
- Steps 2-3: Hard (the main formalization challenge, possibly days)
- Step 4: Easy (follows mechanically)
