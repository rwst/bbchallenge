# BusyLean

Lightweight Lean 4 library for Busy Beaver proofs. Binary alphabet, zipper tape, parametric over state count.

## Architecture

```
Defs.lean          Core types: TM, Config, Sym, Dir, step, run, initConfig
TapeHelpers.lean   ones, zeros, zebra, replicate lemmas, listHead/listTail simp
RunLemmas.lean     run_add, run_halted, step/run left/right locality
Notation.lean      listRepeat (×× n), stA..stF, mkConfig, mkConfigFromTape
Parser.lean        tm! "1RB1RA_..." macro (kernel-reducible)
Tactics.lean       tm_exec, tm_follow, tm_chain, tm_step, tm_ind_succ, tm_ind_zero,
                   evstep_follow, evstep_finish, closeConfigEq_
Nonhalt.lean       nonhalt_of_progress, not_halts_of_progress, halts_of_evstep_halted
Multistep.lean     Multistep/Progress/EvStep relations, notation, Trans instances
ClosedSet.lean     ClosedSet structure + closed_set tactic
Transition.lean    halted_of_step, transReachable, nonhalt_of_unreachable
BackwardReasoning.lean  SymConfig, matchingConfig?, backwardReason, nonhalt_of_backward
StreamDefs.lean    SConfig (infinite tape), toSConfig embedding, commutativity
Attr.lean          tape_norm simp attribute registration
TapeNorm.lean      tape_norm lemmas (cons-fold, append, arithmetic)
EsTactic.lean      `es`, `esx` — symbolic evaluator tactics (batch-stepping + shift rules)
```

## Key design decisions

- **Zipper tape** (`List Sym` left/right + `Sym` head), not mathlib `Turing.Tape`. Enables fast `decide`/`native_decide` on concrete configs.
- **`step` is total**: identity on halted configs (`state = none`). This means `run` always returns a config. The `Progress` relation adds `¬ B.halted` to ensure genuine forward motion.
- **`autoImplicit` is OFF**. All variables must be declared explicitly.
- **No mathlib Turing dependency.** Only mathlib imports are in StreamDefs.lean (for `Nat` lemmas).

## Tape representation

```
Config n = { state : Option (Fin n), left : List Sym, head : Sym, right : List Sym }
```

- `left` is reversed: `left[0]` is immediately left of head
- `ones k` = `List.replicate k true`, `zeros k` = `List.replicate k false`
- `zebra c` = `[false, true, false, true, …]` of length `2c` (alternating 01 pattern)
- `listHead l default` / `listTail l` handle empty lists (read blank / stay empty)
- `mkConfigFromTape n st L R` — extracts head from tape list `R`, defaulting to `false`

## Proving TM behavior

### Concrete runs
```lean
-- Small: decide
example : run tm (initConfig 6) 20 = someConfig := by decide

-- Large: tm_chain (splits into chunks, each proved by decide)
example : run tm (initConfig 6) 500 = someConfig := by tm_chain

-- With variables: tm_exec (step-by-step simp, stops when stuck)
theorem foo : run tm config (k + 22) = config' := by
  tm_exec [tm_def, helper_lemma]

-- With shift lemmas: tm_exec + shifts
theorem bar : run tm config (N + 30) = config' := by
  tm_exec [tm_def] shifts [A_shift, C_shift]
```

### Shift lemmas (inductive)
```lean
lemma A_shift (k : Nat) (L R : List Sym) :
    run tm ⟨some stA, L, true, ones k ++ R⟩ (k + 1) =
    ⟨some stA, ones (k+1) ++ L, listHead R false, listTail R⟩ := by
  induction k generalizing L with
  | zero => rfl   -- or: simp [run, step, tm_def]
  | succ k ih => tm_ind_succ ih stA [tm_def]
```

### Parametric runs (tape locality)
```lean
-- If right tape stays nonempty for k steps, appending T commutes with run
theorem run_right_append (c : Config n) (T : List Sym) (k : Nat)
    (h : ∀ m, m < k → (run tm c m).right ≠ []) :
    run tm { c with right := c.right ++ T } k =
    { run tm c k with right := (run tm c k).right ++ T }

-- Same for left tape
theorem run_left_append ...
```

Pattern: prove a rule on a fixed base tape (by `decide`), then lift to arbitrary tails via locality.

### Non-halting proofs

**Option A: `nonhalt_of_progress`** (functional)
```lean
theorem tm_nonhalt : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  apply not_halts_of_progress tm (fun c => P c)
  · intro c hc  -- show P c implies ∃ k > 0, P (run tm c k) ∧ alive
    ...
  · show P (initConfig 6)  -- or: P (run tm (initConfig 6) k)
    ...
```

**Option B: `closed_set`** (structural, ported from busybeaver)
```lean
theorem tm_nonhalt : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  closed_set (fun c => P c)
  · -- closed: every P-config progresses to another P-config
    intro ⟨c, hc⟩
    exact ⟨⟨c', hc'⟩, k, hk_pos, hrun, hnothalted⟩
  · -- enters: init reaches a P-config
    exact ⟨⟨c₀, hc₀⟩, k₀, hrun₀⟩
```

**Option C: `nonhalt_of_unreachable`** (transition analysis)
```lean
theorem tm_nonhalt : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  apply nonhalt_of_unreachable tm (initConfig 6) (by simp [initConfig, Config.halted])
  intro q s htr  -- for each halting transition (q, s)
  ...            -- show it's unreachable
```

## Multistep notation

```lean
A -[tm]{k}-> B    -- run tm A k = B (Decidable)
A -[tm]->+ B      -- ∃ k > 0, run tm A k = B ∧ ¬ B.halted
A -[tm]->* B      -- ∃ k, run tm A k = B
```

All three support `calc` chaining via `Trans` instances, including mixed types
(e.g., `Multistep` followed by `EvStep`).

### EvStep chaining (BusyCoq's follow/finish)

For proofs that compose many `→*` steps (e.g., mxdys-style macro decomposition):

```lean
-- evstep_follow: chain →* steps
theorem IncsOv3 (a b : ℕ) : S3 a b -[tm]->* S1 0 2 (2+a*2+b) := by
  evstep_follow (Incs3 a b)    -- applies Incs3, reduces goal
  evstep_follow (Ov3 (a*2+b))  -- applies Ov3
  evstep_finish                 -- closes A →* A (or A →* B when A = B up to omega)

-- Or with calc blocks (via Trans instances):
theorem IncsOv3' (a b : ℕ) : S3 a b -[tm]->* S1 0 2 (2+a*2+b) :=
  calc S3 a b
      _ -[tm]->* S3 0 (a*2+b)         := Incs3 a b
      _ -[tm]->* S1 0 2 (2+a*2+b)     := Ov3 (a*2+b)
```

`evstep_follow h` accepts: `EvStep`, `Multistep`, or raw `run tm A k = B` hypotheses.
`evstep_finish` tries: `EvStep.refl`, then `congr 1 <;> omega` on struct fields.

### `es` — symbolic evaluator (`BusyLean/EsTactic.lean`)

`es tm [shift1, shift2, …]` proves `A -[tm]->* B` goals by alternating:
- **Shift rules** (`EvStep` lemmas passed as parameters) — applied via fresh-metavariable
  unification against the current source; absorb many steps at once.
- **Concrete stepping** via `Meta.reduce` on `step tm <src>` — batch up to 30 steps per
  iteration, producing a reduced `Config.mk` literal. Halts on unknown head.
- **`tape_norm` normalization** after each shift/step — folds leading cons prefixes
  back into atoms (`true :: (ones k ++ R) → ones (k+1) ++ R`, etc.).
- **`esFinish`** — three-tier closing: `EvStep.refl`; 0-step + `tape_norm` + `rfl`;
  0-step + four-level `congr 1 / omega` cascade for Nat-index mismatches (e.g.
  `zebra (b+3) = zebra (3+b)`).

```lean
example (b : Nat) :
    ({C, ones 2, t, zebra b ++ [true]} : Config 6) -[tm]->*
    {C, [], t, zebra (3 + b) ++ [true]} := by
  es tm [zebra_traverse_ev, Inc2_boundary_ev, cd_retreat_ev]
```

### `esx` — halts-goal variant

`esx tm [shifts]` proves `∃ k, (run tm A k).halted` by:
1. Reducing via `halts_of_evstep_halted` into `A -[tm]->* ?c` and `?c.halted`.
2. Running the `es` loop with a modified termination: whenever the current source
   has `state := none`, close with `EvStep.refl` (which unifies `?c`).
3. Closing `?c.halted` by `rfl`.

```lean
example : ∃ k, (run tm ({state := some stF, left := [], head := true,
                         right := []} : Config 6) k).halted := by
  esx tm []  -- F with head 1 is a halting transition; halts in 1 step.
```

### `tape_norm` — normalization simp set

Used internally by `es` to fold cons prefixes. Machine-specific atoms can extend
the set by tagging fold lemmas:

```lean
@[tape_norm] theorem rev_zebra_fold_cons_app (k : Nat) (R : List Sym) :
    true :: false :: (rev_zebra k ++ R) = rev_zebra (k + 1) ++ R := rfl
```

### Writing shift rules for `es`

Shift rules are `EvStep` lemmas `{C, L, h, R} -[tm]->* {C', L', h', R'}` with
generic `L` and `R` parameters. The tactic applies them by fresh-metavariable
unification against the current goal source; `forallMetaTelescope` handles the
parameter binders.

Best practices:
- Keep the tape shape on the source **structurally simple** (atom + tail),
  since Lean's `isDefEq` doesn't do tape-unification.
- When an atom needs to be split (`ones (n + m)`, `rev_zebra (k + 1)`), add a
  `@[tape_norm]` fold lemma so the normalization step brings the goal into the
  expected shape.
- For shifts that take extra context on one side, add a second variant with an
  explicit `L`/`R` parameter (e.g. `cd_retreat_ev` vs `cd_retreat_ev_left`).

## Style conventions

- Line width: 100 chars (mathlib convention)
- `native_decide` is frowned upon; prefer structural proofs or `decide`
- Do not set `maxHeartbeats`; proofs should work within defaults
- State abbreviations: `stA` through `stF` for BB(6)
- TM definitions via `tm!` macro, not manual `{ tr := ... }`
