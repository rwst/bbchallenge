# BusyLean Tactic Plan: Best-in-class TM Reasoning

**Goal**: make BusyLean's tactics match or exceed BusyCoq's in expressiveness, so that lemmas like `Inc1`, `Inc2`, `Ov2`, `Inc3`, `Ov3`, `LOv1`, `S1_to_S2`, `ROv1_1_0_halts` can each be proved in **one tactic call**, just as BusyCoq does with `Proof. es. Qed.` or `Proof. esx. Qed.`.

## Status (2026-04-14)

- ✅ **Phase 1** (tape-aware shift matching) — **DONE** in two stages, see `BusyLean/PLAN-tape-unify.md`:
  - **Stage 1 (trailing-empty fallback)**: `esTryShift` retries with each `List Sym` parameter assigned to `[]`, strips `xs ++ []` via `Meta.transform` recognizing both `List.append` (3 args) and `HAppend.hAppend` (6 args), then uses `replaceTargetEq` to coerce the goal type to match the unstripped shift source. Eliminates `_nil` shift variants. Verified on `Inc3_core_base_ev`.
  - **Stage 3 (`tape_split` simp set)**: a separate `BusyLean/TapeSplit.lean` module with context-aware splitting lemmas like `ones_4_peel_2_in : L ++ ones (4 + k) = (L ++ ones 2) ++ ones (2 + k)` (left-associated to match shift sources). Wired in `esTryShift` as a Stage 3 fallback after Stages 0+1 fail; runs `simp only [tape_split]` followed by `simp only [tape_norm]` to re-normalize. Saved/restored around the Stage 3 attempts.
  - Stage 2 (position-aware split) and Stage 4 (brute-force) deferred — not needed for current sorries.
- ✅ **Phase 2** (tape normalization): `BusyLean/Attr.lean` registers the `tape_norm` simp attribute; `BusyLean/TapeNorm.lean` provides cons-fold lemmas for `ones`, `zeros`, `zebra` plus arithmetic simp. `esNormalize` uses `simp only [tape_norm]`. Machine files extend the set with atoms like `rev_zebra`.
- ✅ **Phase 3** (`esx` for halts goals): `esx tm [shifts]` introduced via `halts_of_evstep_halted` + `esxTryHalt` loop. Closes `∃ k, (run tm A k).halted` by detecting reduced `state := none` configs and unifying the existential target with `EvStep.refl`. Verified on a trivial F-state halt.
- ✅ **Phase 4** (polish): four-level `congr 1 / omega` cascade in `esFinish` handles `zebra (b+3) = zebra (3+b)` style mismatches. Tactics documented in `BusyLean/CLAUDE.md`. Still open: `es?` trace mode, `register_option` tuning knobs.

Validated test cases (in `1RB1LA_..../machine.lean`):
- `Inc2_core_base_ev` — `{C, ones 2, t, zebra b ++ [t]} →* {C, [], t, zebra (3+b) ++ [t]}` via `es tm [zebra_traverse_ev, Inc2_boundary_ev, cd_retreat_ev]`. Replaces a ~30-line manual phase decomposition.
- `Inc3_core_base_ev` — `{C, ones 2, t, zebra b} →* {C, [], t, zebra (2+b)}` via `es tm [zebra_traverse_ev_nil, Inc3_boundary_ev, cd_retreat_ev_nil]`. Uses the `_nil` variants for `right := zebra b` (no trailing `++ R`).
- `Inc3_absorb_core_base_ev` — `{C, ones 2, t, zebra b ++ [false]} →* {C, [], t, zebra (2+b)}` via `es tm [zebra_traverse_ev, Inc3_absorb_boundary_ev, cd_retreat_ev_nil]`.
- `esx tm []` proves the trivial F-state halt.

**Lesson learned (informs future Phase 1 work):** Lean's `isDefEq` does not bridge `xs ++ [] = xs`, so shift rules need both `_ev` and `_ev_nil` variants when the right tape can be empty. A future Phase 1 implementation should automate this by retrying unification with each `List Sym` metavariable assigned to `[]` after the direct attempt fails — matching BusyCoq's "context size 0" search.

**Driving observation**: BusyCoq's `es` tactic is the difference between a **3-line proof** and a **150-line manual phase decomposition**. The current Lean `es` (in `EsTactic.lean`) handles single-shift cases but cannot handle multi-cycle macros. Closing this gap is the highest-leverage tactic work in BusyLean.

---

## Status quo (as of 2026-04-14)

`BusyLean/EsTactic.lean` provides `es tm [shift1, shift2, ...]` which:
- Uses `Meta.reduce` to take concrete TM steps (Option 3 — direct MetaM, no `evalTactic` per step)
- Tries shift rules first via `forallMetaTelescope` + `isDefEq`
- Calls `esNormalize` (simp with arithmetic + `replicate_append` + `List.append_*`) after each shift/step
- Closes via `esFinish` (`EvStep.refl` or 0-step + simp)
- Runs in **2-3 seconds** for the full Pillai TM build

**What it can prove automatically**: simple single-shift cases like
```lean
example (b : Nat) :
    ({state := stC, left := [], head := true, right := zebra b ++ [true]} : Config 6)
      -[tm]->* {state := stC, left := rev_zebra b, head := true, right := [true]} := by
  es tm [zebra_traverse_ev]
```

**What it cannot prove**: multi-cycle macros like Inc1, Inc2, Ov2, Ov3, S1_to_S2, ROv1_1_0_halts. These required ~600 lines of manual phase decomposition in `1RB1LA_.../machine.lean`.

---

## What BusyCoq does that we don't (the three key features)

### Feature 1: **Context-size search in shift rule application**

`use_shift_rule` in `Individual33.v:221`:
```coq
let x := match goal with ... shift_rule_L | shift_rule_R end in
  (eapply (x []); find_shift_rule) ||
  (eapply (x [_]); find_shift_rule) ||
  (eapply (x [_;_]); find_shift_rule) ||
  (eapply (x [_;_;_]); find_shift_rule) ||
  ... up to 12 elements ...
```

BusyCoq shift rules take an explicit context list parameter. The tactic tries 13 different sizes (0..12 elements) until one matches. This means a single shift lemma like `cd_retreat_left` can match `rev_zebra k ++ ones 2` OR `rev_zebra k ++ [true, true]` OR `rev_zebra k ++ [true, true, false]` etc., automatically partitioning the tape.

**Lean equivalent**: When `esTryShift` fails to unify a shift rule directly, try unifying after splitting off 0..12 leading symbols from the goal source's tape. This requires tape-aware unification.

### Feature 2: **Tape normalization rewrites baked into stepping**

`Ltac st :=` (Individual33.v:307):
```coq
Ltac st :=
  repeat
  (rewrite lpow_add ||
   rewrite Str_app_assoc ||
   rewrite lpow_mul);
  simpl_tape.
```

Called from `es :=`:
```coq
Ltac es :=
  intros;
  unfold_config;
  repeat (rewrite lpow_add || rewrite Str_app_assoc || rewrite lpow_mul);
  simpl_tape;
  execute_with_shift_rule.
```

BusyCoq normalizes the tape representation aggressively before shift matching. Specifically:
- `lpow_add`: `[a]^^(m+n) = [a]^^m ++ [a]^^n` — splits powers into chunks
- `Str_app_assoc`: tape associativity
- `lpow_mul`: `[a]^^(m*n) = [a]^^m × n times`
- `simpl_tape`: general simplification

Lean already has `esNormalize` but it's much weaker (only `replicate_append` reverse + arithmetic). Need to add:
- Splitting `ones (k+m) = ones k ++ ones m` for various `k`/`m`
- Splitting `zebra (k+m) = zebra k ++ zebra m` similarly
- `rev_zebra`/`zebra` interconversion
- Right-associativity normalization (or left-, consistently)

### Feature 3: **`esx` for halting goals**

`esx` (Individual62.v:767):
```coq
Ltac esx :=
  lazymatch goal with
  | |- _ -[ _ ]->* _ => es
  | |- halts _ _ => solve_halt
  | |- c0 -[ _ ]->* _ => cbn; solve_init
  | |- segRLs _ _ _ _ _ => solve_segRLs
  ...
```

Where `solve_halt`:
```coq
Ltac solve_halt :=
  eapply halts_evstep; [|
    repeat (rewrite lpow_add || rewrite lpow_mul || simpl_tape || simpl_rotate);
    repeat (step1 || sr || simpl_rotate);
    finish
  ];
  eapply halted_halts;
  constructor.
```

For halting goals, `esx`:
1. Reduces `halts c` to `∃ c', c -->* c' ∧ halted c'` via `halts_evstep`
2. Uses concrete steps + shift rules to find a halted state
3. Closes the `halted` predicate via `constructor`

Lean has nothing for this. The current `es` only handles `EvStep`/`Multistep` goals.

---

## Detailed plan (4 phases, ~6 work units total)

### Phase 1: Tape-aware shift matching (the biggest unlock)

**Goal**: when a shift rule's source pattern doesn't directly unify with the goal source, automatically try with a leading prefix split off.

**Concrete behavior**: given goal source `rev_zebra b ++ ones 2 ++ ones (2*a)` and a shift rule expecting `rev_zebra k ++ ones 2 ++ L`, automatically unify with `k := b`, `L := ones (2*a)`. Currently this fails because `ones (2*a)` doesn't reduce.

**Subtask 1.1: `tape_unify` helper**
- Input: two tape expressions `lhs` and `rhs`.
- Try direct `isDefEq lhs rhs`.
- If fails, try splitting `lhs` and `rhs` at common cons prefixes:
  - `(x :: xs) ++ ys = ?` — split as `x :: (xs ++ ys)`.
  - `ones (k+1) ++ ys = ?` — split as `true :: (ones k ++ ys)`.
  - `zebra (k+1) ++ ys = ?` — split as `false :: true :: (zebra k ++ ys)`.
  - `rev_zebra (k+1) ++ ys = ?` — split as `true :: false :: (rev_zebra k ++ ys)`.
- Recurse on the tail until one side bottoms out into a metavariable that can absorb the remainder.

**Subtask 1.2: rewrite `esTryShift` to use `tape_unify`**
- Parse the shift rule's source into `state, left, head, right`.
- Parse the goal source similarly.
- Unify state, head directly (these are concrete).
- Unify `left` and `right` via `tape_unify`.
- If unification succeeds, build the application and replace the goal.

**Subtask 1.3: handle the `++` associativity**
- BusyCoq writes shifts as `rev_zebra k ++ ones 2 ++ L` which Lean parses LEFT-associatively as `(rev_zebra k ++ ones 2) ++ L`. Goal sources after `Meta.reduce` might be RIGHT-associated. The `tape_unify` must canonicalize both sides — pick one direction (right-associative is more natural for cons-style reasoning) and rewrite both sides to match.

**Risk**: tape_unify could be slow if it explores too many splits. **Mitigation**: bound depth at 8 (matching BusyCoq's 12 elements ≈ 8 splits typically) and prune when both sides bottom out.

**Estimated effort**: 200 lines. **Estimated unlock**: solves the unification half of S1_to_S2-style multi-cycle macros.

---

### Phase 2: Stronger normalization

**Goal**: `esNormalize` should handle tape arithmetic well enough that intermediate states after shifts/steps are in a canonical form ready for the next shift match.

**Subtask 2.1: BusyLean's tape rewrite library**
Add a dedicated `BusyLean.TapeNorm` module with these lemmas (most should already exist, just need to be collected):

```lean
-- Splitting (used right-to-left for normalization)
ones_add : ones (k + m) = ones k ++ ones m
zebra_add : zebra (k + m) = zebra k ++ zebra m
rev_zebra_add : rev_zebra (k + m) = rev_zebra m ++ rev_zebra k  -- note the order

-- Cons folding
ones_cons : true :: ones k = ones (k + 1)
zebra_cons : false :: true :: zebra k = zebra (k + 1)
rev_zebra_cons : true :: false :: rev_zebra k = rev_zebra (k + 1)

-- Append-nil
ones_append_nil : ones k ++ [] = ones k
List.append_nil, List.nil_append

-- Associativity (right-normalized)
List.append_assoc

-- Arithmetic normalization (for tape index expressions)
Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, etc.
```

Mark all as `@[tape_norm]` so simp can use them in a controlled set.

**Subtask 2.2: rewrite `esNormalize`**
- Use `simp only [tape_norm]` instead of the current ad-hoc list.
- Make the direction of `ones_add`/`zebra_add` configurable (split vs merge) — default to **split** (we want the fine-grained form for unification).

**Subtask 2.3: handle multiplication**
BusyCoq's `lpow_mul` handles `[a]^^(m*n) = [a]^^m ^^ n`. For Lean, the analog is `ones (m*n) = (ones m).join`-style — usually we'd just rewrite to `ones m ++ ones m ++ ... ++ ones m` (n times). Defer this until needed.

**Estimated effort**: 100 lines (mostly collecting and tagging existing lemmas). **Estimated unlock**: complements Phase 1 — the two together should solve Inc2, Ov2, Inc3, Ov3, S1_to_S2 automatically.

---

### Phase 3: `esx` for halting goals

**Goal**: extend `es` to handle goals of form `(run tm c k).halted` or `∃ k, (run tm c k).halted` automatically.

**Subtask 3.1: BusyLean halting infrastructure**
Verify these exist in `BusyLean/Nonhalt.lean` (or add them):
- `halts (c : Config n) : Prop := ∃ k, (run tm c k).halted` (or similar)
- `halts_of_evstep_halted : c -[tm]->* c' → c'.halted → halts c`
- `halted_of_state_none : c.state = none → c.halted` (or this is definitional)

**Subtask 3.2: `esStep1_halted`**
A variant of `esStep1` that:
- Takes a step via `Meta.reduce`
- After the step, checks if `cur.state = none`
- If so, closes the halting goal directly (no need to build a chain).
- Otherwise, behaves like the current `esStep1`.

**Subtask 3.3: `esx` driver**
```lean
syntax "esx " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| esx $tmId [ $shifts,* ]) => do
    -- Inspect goal type
    let goal ← getMainGoal
    let goalType ← goal.getType
    match parseGoal goalType with
    | .evstep => evalEs tmId shifts  -- existing es
    | .halts => do
        -- Reduce `halts c` to `∃ c', evstep c c' ∧ halted c'` via halts_evstep
        evalTactic (← `(tactic| apply halts_of_evstep_halted))
        evalEs tmId shifts
        -- Final goal: c'.halted, close by `decide` or rfl
        evalTactic (← `(tactic| decide))
    | .none => throwError "esx: unsupported goal shape"
```

**Subtask 3.4: existential halting goal**
For Lean's `∃ k, (run tm c k).halted`:
- Build the witness `k` as we go (count steps taken)
- Provide `⟨k, ...⟩` at the end

This requires tracking step count in the tactic monad — `esStepN` already returns the count, so accumulate.

**Estimated effort**: 150 lines. **Estimated unlock**: ROv1_1_0_halts and any other halting-case lemma.

---

### Phase 4: Polish and integration

**Subtask 4.1: better error messages**
When `es` fails, print:
- The current goal (already done)
- Which shifts were tried and why each failed (currently silent)
- The reduced source expression

**Subtask 4.2: `es?` mode (debug trace)**
Add a `set_option es.trace true in es tm [...]` mode that logs each phase's transition (state, head, step count). Helps users debug stuck proofs.

**Subtask 4.3: Lean-style configuration**
Replace the hard-coded constants in EsTactic with options:
```lean
register_option es.maxIterations : Nat := { defValue := 200, ... }
register_option es.batchSize : Nat := { defValue := 30, ... }
register_option es.shiftSearchDepth : Nat := { defValue := 8, ... }
```

**Subtask 4.4: documentation**
Update `BusyLean/CLAUDE.md` with:
- Description of `es` and `esx` syntax
- Examples of working and failing cases
- Cookbook for adding new shift rules and contexts

**Estimated effort**: 100 lines + docs. **Estimated unlock**: better DX, easier debugging.

---

## Validation checkpoints

### Checkpoint A (after Phase 1 + 2)
**Test**: re-run the existing manual proofs in `1RB1LA_.../machine.lean` for `Inc2`, `Ov2_raw`, `Inc3_absorb`, `Ov3` and replace each with `es tm [shift_list]`. They should all compile.

**Stretch**: also `S1_to_S2` should work.

### Checkpoint B (after Phase 3)
**Test**: replace `ROv1_1_0_halts` with `esx tm [shift_list]`. Should compile.

### Checkpoint C (after Phase 4)
**Test**: `es?` debug mode produces useful traces. New TM proof file uses `es`/`esx` as primary tactics, with manual phase decomposition only for theorems requiring induction (`P_n`, `Incs1`, `Incs2`, `Incs3`).

---

## Order of operations

1. **Start with Phase 2** (tape normalization library) — easiest, builds confidence, prerequisite for Phase 1.
2. **Then Phase 1** (tape-aware shift matching) — biggest unlock, but harder.
3. **Then Phase 3** (esx for halting) — straightforward extension.
4. **Phase 4** (polish) — last.

---

## Non-goals

- **Not** porting BusyCoq's stream/0inf representation. Lean's finite tape is sufficient for individual machine proofs.
- **Not** porting BusyCoq's `solve_seg`/`segRL`/`segLL` machinery (used for very long-period TMs). Out of scope for now.
- **Not** porting BusyCoq's macro-based proof scripts. The Lean approach is one tactic per atomic rule, calc-chained.

---

## Files to touch

- **New**: `BusyLean/BusyLean/TapeNorm.lean` — tape normalization lemma collection (Phase 2)
- **Modified**: `BusyLean/BusyLean/EsTactic.lean` — Phase 1 (tape_unify), Phase 3 (esx), Phase 4 (options)
- **Modified**: `BusyLean/BusyLean/Nonhalt.lean` — Phase 3 helper lemmas (if missing)
- **Modified**: `BusyLean/CLAUDE.md` — Phase 4 docs
- **New**: `BusyLean/TODO.md` — mark items 12 and 14 as superseded by this plan

---

## Estimated total effort

| Phase | Lines | Effort |
|---|---|---|
| Phase 2 (normalization) | 100 | 1 work unit |
| Phase 1 (tape unify) | 200 | 2 work units |
| Phase 3 (esx) | 150 | 1.5 work units |
| Phase 4 (polish) | 100 | 0.5 work units |
| **Total** | **~550** | **~5 work units** |

After completion, the Pillai proof file (`1RB1LA_.../machine.lean`) should shrink from ~1100 lines (current, with manual macro proofs) to ~400 lines (with `es`/`esx` doing the work). Net savings: ~700 lines moved from the proof file into the tactic library where they're reusable across all future TM proofs.

## Beyond Pillai

Once the tactics are at parity with BusyCoq, the next BB(6) holdout machines that BusyCoq has proved should be portable in ~1 day each (vs the current ~1 week per machine). The tactic investment pays for itself after 2-3 machines.
