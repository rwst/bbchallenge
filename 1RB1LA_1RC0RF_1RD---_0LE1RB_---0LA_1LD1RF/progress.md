# Proof Progress Report: 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

## Summary

- **Proven**: E0Inv + e0_never_reached (E,0 fully eliminated)
- **Remaining sorry**: 2 (`c1_never_reached`, `sweeper_never_halts`)
- **`sweep_left_zero_shift` removed** (was wrong, not needed)

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

## Remaining Sorries (2)

### 1. `c1_never_reached` (line ~280) — **HARD: RIGHT-TAPE INVARIANT**

**Statement**: For all k, either the machine after k steps is not in
state C, or the head reads 0 (false).

**Status**: C1Inv defined in Lean with 4 conditions (B, A, C, D). Step
proof (`c1inv_step`) closes 11/12 transition cases. Sole remaining sorry
is E,1→0LA, which requires the F-joint condition (see below).

### 2. `sweeper_never_halts` (line ~418) — **FOLLOWS FROM c1 + e0**

**Statement**: For all k, `(run sweeper (initConfig 6) k).state ≠ none`.

**Dependency**: Follows from `c1_never_reached` (proven: no) and
`e0_never_reached` (proven: yes). Once c1 is proved, this should be
straightforward.

## Proven Sorries

### `e0_never_reached` — **PROVEN** via E0Inv step-inductive invariant

Uses 4-condition E0Inv on left tape structure. Proof pattern:
`fin_cases q <;> cases hd <;> simp [...] <;> simp_all [...]`
with one extra `intro h; simp_all` for the F,0→D case.

---

## Simulation Findings for c1_never_reached

### B,0 event analysis (200K+ steps)

1. **C always reads 0**: At every B,0 event, `listHead B.right false = false`. Confirmed over 200K steps (203 B,0 events in first 1M steps).

2. **B→C→D chain depth is always ≤ 2**: The chain B,0→C,0→D→... never recurses more than twice. Distribution over 1M steps: depth 1 = 178 occurrences, depth 2 = 25 occurrences.

3. **Depth-2 B always has all-zero right tape**: When B,0 comes from D (via B→C→D→B' chain), B'.right is always all-zeros. This is the "right tape edge" BCD extension.

4. **B,0 sources**: B,0 comes from A,0→1RB (depth-1, majority) or from D,1→1RB via C,0→1RD (depth-2, always at right edge). D always enters from C (prev_prev_state = C).

5. **A,0 after sweep always has right starting with true**: When A reads 0 after sweeping through ≥1 ones, A.right always starts with 1 (true). So B reads 1 and never triggers C entry. B reads 0 ONLY when A reads 0 immediately after E→A (sweep_count = 0).

6. **A.right at B,0 events**: A.right always = `[0, 0, D_right...]` where D_right starts with 1 (true) or 0 (false). When D_right[0] = 1, the subsequent B→C→D chain reads into D_right but always terminates safely.

7. **Triple zeros on tape**: Three consecutive zeros appear transiently (for 1-2 steps) during BCD extension phases, but max consecutive zeros at any snapshot is 2. Triple zeros appear when state A or F reads 0 at a double-zero boundary, and disappear when A→B or F→D writes 1.

### Key structural insights for c1_never_reached

**Insight 1**: B reads 0 ONLY when A reads 0 directly from E→A transition
(sweep_count = 0). When A sweeps through ≥1 ones first, A.right starts with
true (from accumulated ones), so B reads 1. Confirmed over 200K steps.

**Insight 2**: At A,0 from E→A, A.right = `false :: false :: D_right` where
D_right comes from the preceding BCD extension. B.right = `false :: D_right`.
B.right[0] = false → C reads 0 (safe).

**Insight 3**: The B→C→D chain has period-3 structure. Starting from B.right:
- Position 0 (C reads): always false ✓
- Position 1 (D reads): true or false
- Position 2 (B' reads): true (safe) or false (recurse)
Each recursion consumes 3 elements. SafeRight predicate verified for 1M steps.

**Insight 4**: At interior BCD events, F.left ALWAYS has k_left_ones = 0
(F.left starts with `[0, 1, ...]`). This means D.left starts with `[1, ...]`,
E.left starts with `[...]`, A.head = E.left[0] = F.left[2].

**Insight 5 (CRITICAL)**: When F.right starts with `[0, 1, ...]` (the
"dangerous" pattern for SafeRight), F.left[2] is ALWAYS 1. This means
A.head = 1, so A sweeps left before reading 0, and B never sees the
dangerous pattern. Confirmed over 500K steps (no violations found).

**Insight 6**: When F.left[2] = 0 (A reads 0 immediately), F.right starts
with `[0, 0, ...]` or `[1, ...]` — never `[0, 1, ...]`. So the right tape
reaching B is always SafeRight.

### Proposed invariant for c1_never_reached

**SafeRight** (period-3 recursive on B.right):
```
SafeRight([]) = True
SafeRight(true :: _) = False  -- C reads 1 → halt (never happens)
SafeRight(false :: []) = True
SafeRight(false :: false :: _) = True  -- D reads 0, BCD
SafeRight(false :: true :: []) = True
SafeRight(false :: true :: true :: _) = True  -- B' reads 1, safe
SafeRight(false :: true :: false :: rest) = SafeRight(rest)  -- recurse
```

**Step-inductive closure**: C1Inv with B, A, C (SafeRight1), D (SafeRight2)
conditions closes 11/12 cases. The sole remaining case is E,1→0LA.

### c1inv_step: case analysis results (Lean)

| Transition | Status | How |
|---|---|---|
| A,1→1LA | ✓ | `listHead(true::R)=true` → Or.inl |
| A,0→1RB | ✓ | A-condition directly gives B-condition |
| B,0→1RC | ✓ | vacuous (state=C) |
| B,1→0RF | ✓ | vacuous (state=F) |
| C,0→1RD | ✓ | SafeRight1_to_SafeRight2 |
| C,1→none | ✓ | halted, vacuous |
| D,1→1RB | ✓ | SafeRight2_to_SafeRight |
| D,0→0LE | ✓ | vacuous (state=E) |
| E,0→none | ✓ | halted, vacuous |
| **E,1→0LA** | **sorry** | **needs SafeRight(E.right) when E.left[0]=false** |
| F,0→1LD | ✓ | SafeRight2(true :: R) = True |
| F,1→1RF | ✓ | vacuous |

### E,1→A sorry: detailed analysis

E enters only from D,0. Two paths:

**C→D→E**: E.left = `true :: B.left`. `listHead(E.left) = true`. A reads 1. **Vacuous** ✓

**F→D→E**: E.right = `false :: true :: F.right`. E.left[0] = F.left[2].
- F.left[2] = true: A reads 1. Vacuous ✓
- F.left[2] = false: need `SafeRight(false :: true :: F.right)`.

`SafeRight(false :: true :: F.right)` is True when:
- F.right = `[]` → True ✓
- F.right starts with true → True ✓
- F.right = `false :: false :: _` → `SafeRight(false :: _) = True` ✓
- F.right = `false :: true :: rest` → `SafeRight(rest)` ← **ONLY DANGEROUS CASE**

**Simulation (1M steps)**: When F.left=[0,1,0,...], F.right NEVER starts with
`false :: true :: ...`. It's always empty or starts with true. So the dangerous
case never occurs. `SafeRight(false :: true :: F.right)` confirmed True at all
such events. When F.right starts with false, it's always `[]` (right tape edge).

### The F-joint condition (sole remaining obstacle)

The proof obligation reduces to:

```
F.head=false → F.left[0]=false → F.left[2]=false →
  SafeRight(false :: true :: F.right)
```

This holds trivially when F.right starts with true or is empty. The only
dangerous case (F.right = `false :: true :: rest`) never occurs because when
F.left[2]=false, F is at the last zero-marker and F.right is blank tape.

**Why it's hard to prove**: this couples F.left[2] with F.right structure —
a left/right correlation depending on zero-marker spacing (global tape property).

### Alternative approaches considered

1. **AllFalse(B.right)**: TOO STRONG — interior BCD creates true values.
2. **EvenFalse (period-2)**: Wrong alignment — B→C→D shifts by 3.
3. **Position-based**: hard in zipper representation.
4. **Phase-aware structural**: most general but most work.

### Mathematical obstacles for c1_never_reached

#### Obstacle 1: The invariant cannot be local on B.right alone

B is entered from two sources:
- **A,0 → 1RB**: B.right = listTail(A.right). A.right depends on where A
  bounced — at the right edge it's `false :: false :: zeros p` (safe), but
  at an interior zero it's whatever the tape looks like at that point.
- **D,1 → 1RB** (interior BCD chain): B.right = listTail(D.right). This is
  the previous B.right shifted by 2, so SafeRight recurses correctly (period-3).

The D,1→B case works with SafeRight's period-3 recursion. The A,0→B case
is the problem: the NEW B.right comes from the global tape structure at the
bounce point, not from a local transformation of the old B.right.

#### Obstacle 2: F.left/F.right coupling through unbounded F-sweeps

During an F-sweep, F bounces at 0, 1, 2, ... interior zeros. At each bounce:
- F.left gets `false :: ones(k) ++` prepended
- F.right advances past the consumed zero

The joint condition (F.right=[0,1,...] → F.left[2]=1) at bounce i depends on
what happened at bounce i-1. After f_bounce_interior + F_shift, F.left =
`ones(m) ++ false :: ones(k+1) ++ L_prev`. The value of F.left[2] at the
next bounce depends on m (distance between consecutive zeros).

**This is a non-local property**: the correlation between F.left[2] and F.right
depends on the spacing between zero-markers, which is a global tape property.
No finite-depth local condition on F can capture it without also characterizing
the zero-marker positions.

#### Obstacle 3: Circularity between macro-step and single-step approaches

**Macro-step approach** (prove invariant per sweep cycle):
- Must prove the sweep cycle COMPLETES without halting — which IS the theorem.
- Must prove f_bounce_interior applies at each interior zero (requires k≥1
  ones to the left) — which is part of the tape invariant.
- Result: circular. Can't prove cycle completion without the invariant,
  can't prove the invariant without cycle completion.

**Single-step approach** (prove invariant per TM step):
- Avoids circularity but the invariant must hold at ALL intermediate configs.
- The joint F condition shifts during F,1→1RF steps (ones accumulate on left).
- SafeRight on B.right is meaningless when the machine is not in state B.
  Need equivalent conditions for A, D, E, F states that imply SafeRight
  when B is eventually re-entered — these are hard to formulate.

**Hybrid approach** (phase-aware step-inductive invariant):
- Define different conditions per state (like E0Inv does).
- For B: SafeRight(B.right) when B.head = false.
- For F: the joint condition on F.left/F.right.
- For A: ??? — A.right must produce SafeRight(listTail(A.right)) when
  A reads 0, but A.right changes as A sweeps (ones move from left to right).
  The SafeRight property must be invariant under prepending ones, which it IS
  (SafeRight(true :: rest) = False, but we need SafeRight(rest), and prepending
  true to right during A sweep shifts the condition). Actually, A,1→1LA moves
  a true from left to right, so A.right = true :: old_A.right after one step.
  SafeRight(true :: R) = False, which is wrong! A's right tape has trues
  prepended, so SafeRight doesn't hold for A.right during A-sweep.

  **This means SafeRight cannot be a uniform condition across all states.**
  It only makes sense for B.right, and we need per-state translations that
  track how the tape transforms between state entries.

#### Obstacle 4: SafeRight has unbounded depth vs transitions shift by 1

SafeRight recurses at period 3 (consuming 3 elements per B→C→D chain
iteration). The D,1→B re-entry shifts by 3, matching the recursion — fine.

But at A,0→B entry (new sweep cycle), B.right is COMPLETELY NEW. It's the
right tape at the point where A bounced. SafeRight for this new B.right must
be established from scratch from the previous sweep cycle's tape structure.

This requires an induction on sweep cycles, not single steps. Formalizing
"sweep cycle" in the zipper representation requires knowing the exact step
count (depends on tape length and zero positions), making it hard to express
as a Lean induction.

#### Obstacle 5: E0Inv's success is misleading

E0Inv works because:
- Each condition is ≤2 cells deep (listHead, listHead∘listTail)
- Conditions are on ONE side of the tape only (left)
- Each transition locally preserves or re-establishes the condition

C1Inv fails this pattern because:
- SafeRight has unbounded depth
- The joint condition couples BOTH sides of the tape
- Re-establishment at A,0→B requires global tape knowledge

### Difficulty assessment

## Recommended Next Steps

1. **Prove the F-joint condition**: The SOLE remaining obstacle.
   Need: `F.head=false → F.left[0]=false → F.left[2]=false → SafeRight(false :: true :: F.right)`
   
   Possible approaches:
   - Add as C1Inv condition, prove step-inductive through F creation and F-bounce
   - Prove structurally that F.left=[0,1,0,...] implies F is at last zero-marker
     (so F.right is blank tape — empty or all-ones)
   - Full IsReachable: characterize all reachable tape shapes per state

2. **Derive `sweeper_never_halts`**: Once c1 is proved, combine with e0_never_reached.
