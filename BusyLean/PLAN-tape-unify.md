# BusyLean: Phase 1 — `tape_unify` (real implementation)

**Goal**: make `esTryShift` automatically bridge defeq gaps caused by the
mismatch between **merged-atom** goals and **split-atom** shift rules. Eliminate
the need for `_nil`, `_keep_ones`, and other one-off shift variants.

**Reference**: BusyCoq's `Individual33.v:209-272`, specifically `find_shift_rule`,
`use_shift_rule`, `shift_rule_L`, `shift_rule_R`.

---

## What BusyCoq actually does

BusyCoq has **one** generic lemma `shift_rule_L` (and `shift_rule_R`) that
*lifts* a 1-iteration shift to N iterations:

```coq
Lemma shift_rule_L d tm x x' X:
  (forall l r,
    l <* x <{{X}} d *> r -[ tm ]->*
    l <{{X}} d *> x' *> r) ->
  forall l r n,
    l <* x^^n <{{X}} d *> r -[ tm ]->*
    l <{{X}} d *> x'^^n *> r.
```

The user's actual shift lemmas are **1-iteration** rules: for each cell-pattern
they want to handle (`[1]`, `[0;1]`, `[1;1]`, …), they prove a single forall
lemma `forall l r, l <* pattern <{{X}} d *> r -->* l <{{X}} d *> pattern' *> r`.

The `use_shift_rule` tactic then iterates over **segment lengths** by passing
list literals of progressively more underscores:

```coq
(eapply (shift_rule_L []);    find_shift_rule) ||
(eapply (shift_rule_L [_]);   find_shift_rule) ||
(eapply (shift_rule_L [_;_]); find_shift_rule) ||
…
(eapply (shift_rule_L [_;_;_;_;_;_;_;_;_;_;_;_]); find_shift_rule)
```

Each `eapply` instantiates `x` to a list of fresh metavariables of a specific
length. `find_shift_rule` then proves the 1-iteration premise from the local
context (or a known hypothesis). When a length matches, the metas are unified
with the actual cell symbols.

**This is BusyCoq's "context-size search"**: try every segment length 0..12 and
let unification pick.

---

## Why this doesn't translate directly to BusyLean

Our shift rules are **already N-iteration** EvStep theorems with the count
baked in:

```lean
theorem zebra_traverse_ev (b : Nat) (L R : List Sym) :
    ({C, L, t, zebra b ++ R} : Config 6) -[tm]->*
    {C, rev_zebra b ++ L, t, R}
```

There is no `shift_rule_L` lifting because the iteration `b` is already a
parameter. We don't need to vary the segment length — `b` does that.

What we *do* need is a way to bridge **merged-atom vs split-atom** mismatches:

| Goal source                                    | Shift expects                          | Defeq? |
|-----------------------------------------------|----------------------------------------|:------:|
| `rev_zebra (b+1) ++ ones (4+2a)`              | `rev_zebra k ++ ones 2 ++ L`           | ❌    |
| `zebra b`                                     | `zebra ?b ++ ?R`                       | ❌    |
| `ones (k+m) ++ ones (4+2c) ++ T`              | `ones n ++ T'`                         | ❌    |

The goal has **collapsed** atoms (`ones (4+2a)`); the shift wants a **split**
form (`ones 2 ++ L`). Lean's `isDefEq` doesn't perform `ones a ++ ones b →
ones (a+b)` reductions because they're not definitional.

---

## Plan: `tape_unify` for BusyLean

A four-stage fallback in `esTryShift` that retries unification after various
goal/shift normalizations.

### Stage 0 (current): direct `isDefEq`

Already implemented. ~40 lines. Handles the easy cases.

### Stage 1: trailing-empty fallback

For each `List Sym` metavariable in the shift's parameter list, try assigning
it to `[]` and stripping the resulting `xs ++ []` patterns. Retry `isDefEq`.

This handles the `zebra b` (no trailing R) case, eliminating the need for
`_nil` shift variants.

**Implementation**:

```lean
private def stripAppendNil (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (post := fun e' => do
    if e'.isAppOfArity ``List.append 3 then
      let ys := e'.getArg! 2
      if ys.isAppOf ``List.nil then
        return .done (e'.getArg! 1)
    return .done e')

-- In esTryShift, after direct isDefEq fails:
for i in [:8] do
  let restore ← saveState
  let mvId := mvars[i]!.mvarId!
  if !(← mvId.isAssigned) then
    let mvTy ← mvId.getType
    if ← isDefEq mvTy listSymTy then
      try mvId.assign nilSym catch _ => continue
      let shiftSrc' ← stripAppendNil shiftSrc
      if ← isDefEq goalSrc shiftSrc' then
        -- success — also strip shiftB and continue
        let shiftB' ← stripAppendNil shiftB
        ...
        return true
      restore.restore
```

**Subtlety from earlier failed attempt**: assigning every List Sym mvar to `[]`
at once (rather than one at a time) clobbers mvars that should unify with
non-empty content. Iterate and try one at a time, restoring state on each
failure.

### Stage 2: atom-prefix split fallback

When the shift's source contains `atom n ++ L` (with concrete `n`) and the
goal has `atom (n + ?_)` (merged form), split the goal's atom.

**Recognition**: walk both the goal and the shift's source in parallel.
Identify positions where the shift has `ones n ++ ?L` (or zebra/zeros/...)
and the goal has `ones e` for some `e` of the form `Nat.add n e'` or
`Nat.add e' n` (after Nat normalization).

**Action**: rewrite the goal's `ones (n + e')` to `ones n ++ ones e'` via
`(ones_append n e').symm`, then retry `isDefEq`.

**Implementation**:

```lean
private structure SplitCandidate where
  /-- Position in the goal expression to rewrite. -/
  loc      : SubExpr.Pos
  /-- The "split off" atom count (e.g. 2, 4). -/
  prefixN  : Nat
  /-- The remaining part (e' such that the original atom was `ones (prefixN + e')`). -/
  remainder : Expr

private def findSplitCandidates (shiftSrc goalSrc : Expr) :
    MetaM (Array SplitCandidate) := do
  -- Walk shiftSrc looking for `atom n ++ ?L` patterns where n is a literal.
  -- For each, walk the corresponding position in goalSrc and look for
  -- `atom e` where e contains n as an addend.
  ...

private def applySplit (cand : SplitCandidate) : TacticM Unit := do
  -- Rewrite the goal at cand.loc using `ones_append`.symm or zebra_append.symm.
  let eqProof ← mkAppM ``ones_append.symm
    #[mkNatLit cand.prefixN, cand.remainder]
  evalTactic (← `(tactic| rewrite [show $... from $eqProof]))
```

Note: `ones_append : ones a ++ ones b = ones (a+b)`. We use the `.symm` to
rewrite right-to-left (split direction). But this conflicts with `tape_norm`
which rewrites left-to-right (merge). To avoid loops:

- The split rewrite is applied **only at the specific position** (not
  globally via simp).
- After matching the shift, the post-shift `esNormalize` re-merges everything
  via `tape_norm`. The split is transient.

### Stage 3: arithmetic normalization fallback

When `ones (n + e)` doesn't directly match `ones (m + ?_)` because `n` and `m`
are different literals (e.g., goal has `ones 4`, shift wants `ones 2 ++ L`),
try unifying via `omega`:

```
omega-driven rewrite: ones (4 + 2*a) = ones (2 + (2 + 2*a))
                                    = ones 2 ++ ones (2 + 2*a)
```

**Implementation**: for each shift's `ones n` atom, try the goal's `ones e` with
`n ≤ e_concrete` (if e has a concrete component). Construct the rewrite via
`omega`-derived nat equality + `ones_append.symm`.

```lean
private def tryArithSplit (n : Nat) (goalAtom : Expr) : MetaM (Option Expr) := do
  -- goalAtom is `ones e`. Want to rewrite to `ones n ++ ones (e - n)`.
  -- Need e ≥ n, expressible via omega.
  let e := goalAtom.getArg! 0
  -- Build proof: e = n + (e - n), or omega proves it
  let eqProof ← mkAppM ``Nat.eq_add_of_sub_eq #[??]
  -- Use eqProof + ones_append.symm to rewrite
  ...
```

This is the trickiest stage. The challenge: `e - n` may not reduce, so we'd
get `ones (e - n)` which still has Nat subtraction. We can substitute via
`Nat.add_sub_cancel` or equivalent.

**Alternative**: instead of computing `e - n`, introduce a fresh metavariable
`?k` and add the constraint `e = n + ?k`. Use `omega` to discharge the
constraint when `?k` is later instantiated.

```lean
let ?k ← mkFreshExprMVar (mkConst ``Nat)
let constraint ← mkAppM ``Eq #[e, mkAppM ``HAdd.hAdd #[mkNatLit n, ?k]]
-- Try omega to satisfy
let omegaProof ← Meta.evalTactic (← `(tactic| omega)) on constraint
-- Rewrite using omegaProof
```

Too fragile. **Better approach**: add a **dedicated splitting simp set**
`tape_split` with conditional rules:

```lean
register_simp_attr tape_split

@[tape_split] theorem ones_split_2 (k : Nat) (L : List Sym) :
    ones (2 + k) ++ L = ones 2 ++ (ones k ++ L) := by
  rw [List.append_assoc, ones_append]

@[tape_split] theorem ones_split_4 (k : Nat) (L : List Sym) :
    ones (4 + k) ++ L = ones 4 ++ (ones k ++ L) := by
  rw [List.append_assoc, ones_append]

-- Similar for k + 2, k + 4 forms
@[tape_split] theorem ones_split_2_r (k : Nat) (L : List Sym) :
    ones (k + 2) ++ L = ones k ++ (ones 2 ++ L) := by ...
```

`esTryShift` runs `simp only [tape_split]` on the goal as a fallback rewrite,
THEN retries `isDefEq`. Multiple variants for different split points
(`2`, `4`, `6`).

This avoids the arithmetic complexity by enumerating common split sizes.

### Stage 4 (optional): brute-force segment search

If all of the above fail, try the BusyCoq-style search by progressively
splitting the goal into more pieces. Bounded depth (e.g., 4 nested splits).

---

## Recommended implementation order

1. **Stage 1 (trailing-empty fallback)** — ~50 lines, eliminates `_nil`
   variants. Verified failed attempt last session; need to fix the "assign
   one mvar at a time, restore between" pattern.

2. **Stage 3 (`tape_split` simp set)** — ~80 lines, adds splitting lemmas
   and a fallback simp pass. Handles the `ones (4+2a)` vs `ones 2 ++ L` case
   (which blocks S1_to_S2 via es).

3. **Stage 2 (position-aware split)** — ~150 lines, more surgical. Only do
   this if Stage 3 isn't sufficient.

4. **Stage 4** — skip unless multi-atom contexts demand it.

---

## Concrete file layout

- **New**: `BusyLean/BusyLean/TapeSplit.lean` — splitting lemmas tagged
  `@[tape_split]`. ~60 lines.
- **New attribute**: add `tape_split` to `BusyLean/Attr.lean`. ~5 lines.
- **Modified**: `BusyLean/BusyLean/EsTactic.lean` — replace `esTryShift` with
  multi-stage version. ~200 lines (replaces the current ~30-line version).
- **Modified**: `1RB1LA_..../machine.lean` — remove `_nil` and `_keep_ones`
  shift variants, simplify es invocations.

---

## Validation checkpoints

After each stage, re-test:

- **Inc2_core_base_ev** via `es tm [zebra_traverse_ev, Inc2_boundary_ev,
  cd_retreat_ev]` — should still work (Stage 0).
- **Inc3_core_base_ev** via `es tm [zebra_traverse_ev, Inc3_boundary_ev,
  cd_retreat_ev]` (without `_nil` variants) — passes after Stage 1.
- **Inc1_core_base_ev** via `es tm [zebra_traverse_ev, ones_process_ev,
  cd_retreat_ev_left]` — passes after Stage 3 (handles `ones (4+2c)` split).
- **S1_to_S2** via `es tm [zebra_traverse_ev, Inc2_boundary_ev,
  cd_retreat_ev_left, ones_process_ev, ...]` — partial Stage 3, full
  validation after Stage 4.

---

## Lessons from the failed attempt (this session's blueprint)

In the previous session I tried implementing Stage 1 with `Meta.transform` +
mvar-at-a-time assignment but every attempt reported "fallback i=N failed"
for all N. The fix needed:

1. **Don't reuse `mvars` across attempts**: each `attempt` should
   re-elaborate `shiftSyn` from scratch, getting fresh mvars. The existing
   code does this correctly via `Term.elabTerm shiftSyn none` inside
   `attempt`, so re-elaboration is fine.

2. **Verify `stripAppendNil` actually fires**: the `Meta.transform` post-walk
   should match `List.append _ xs nil` and rewrite to `xs`. The earlier
   debug showed all 8 indices failing — likely because either the walk
   wasn't recognizing `List.nil` (different form?) or the goal/shift were
   not syntactically aligned even after stripping.

3. **Add a successful direct-defeq baseline test** before testing the
   fallback. The failed session showed Tests 2 and 3 (which previously
   worked via direct defeq) ALSO regressing — suggesting the refactored
   `esTryShift` broke something orthogonal, possibly the `mkAppM
   ``EvStep.trans` step expecting the original `shiftB` while getting
   `shiftB'`. **Fix**: in the direct path, never strip; only strip when
   `preAssignIdx.isSome`.

4. **Test stripAppendNil in isolation** with `lean_run_code` before
   integration. Use a sample expression like `List.append _ [a, b] []` and
   verify it returns `[a, b]`.

---

## Estimated effort

| Stage | Lines | Effort | Unlock |
|---|---|---|---|
| Stage 1 (trailing-nil) | 60 | 0.5 day | Inc3, esx halt traces |
| Stage 3 (tape_split simp) | 100 | 1 day | Inc1, S1_to_S2 (partial) |
| Stage 2 (position split) | 150 | 1.5 days | full S1_to_S2 |
| Stage 4 (brute search) | 80 | 0.5 day | edge cases |
| **Total** | **390** | **~3.5 days** | full BusyCoq parity |

After completion, the machine file's shift-rule boilerplate (the `_nil`,
`_keep_ones`, `_left_cons` variants, plus parameterized `_gen` versions)
can be deleted — net savings ~150 lines.
