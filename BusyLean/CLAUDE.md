# BusyLean

Lightweight Lean 4 library for Busy Beaver proofs. Binary alphabet, zipper tape, parametric over state count.

## Architecture

```
Defs.lean          Core types: TM, Config, Sym, Dir, step, run, initConfig
TapeHelpers.lean   ones, zeros, replicate lemmas, listHead/listTail simp
RunLemmas.lean     run_add, run_halted, step/run left/right locality
Notation.lean      listRepeat (×× n), stA..stF, mkConfig (⟪ q | l | h | r ⟫)
Parser.lean        tm! "1RB1RA_..." macro (kernel-reducible)
Tactics.lean       tm_exec, tm_follow, tm_chain, tm_step, tm_ind_succ, tm_ind_zero
Nonhalt.lean       nonhalt_of_progress, not_halts_of_progress
Multistep.lean     Multistep/Progress/EvStep relations with notation
ClosedSet.lean     ClosedSet structure + closed_set tactic
Transition.lean    halted_of_step, transReachable, nonhalt_of_unreachable
BackwardReasoning.lean  SymConfig, matchingConfig?, backwardReason, nonhalt_of_backward
StreamDefs.lean    SConfig (infinite tape), toSConfig embedding, commutativity
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
- `listHead l default` / `listTail l` handle empty lists (read blank / stay empty)

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

## Style conventions

- Line width: 100 chars (mathlib convention)
- `native_decide` is frowned upon; prefer structural proofs or `decide`
- Do not set `maxHeartbeats`; proofs should work within defaults
- State abbreviations: `stA` through `stF` for BB(6)
- TM definitions via `tm!` macro, not manual `{ tr := ... }`
