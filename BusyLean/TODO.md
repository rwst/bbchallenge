# BusyLean TODO: Lessons from Antihydra + BusyCoq Comparison

## Current state

BusyCoq AntiHydra.v: ~100 lines (Coq)
Antihydra.lean: ~678 lines (Lean, after `tm_exec` + auto-shift + StreamDefs)

The ~7x gap is explained by both missing BusyLean features and fundamental
architectural differences. This document catalogs what needs to change.

---

## BusyLean features applied to Antihydra

| Feature | Applied? | Notes |
|---------|----------|-------|
| `tm!` macro | Yes | TM definition |
| `stA`..`stF` | Yes | Throughout |
| `ones`/`zeros` | Yes | Throughout |
| `run_add` | Yes | Backbone of every chained proof |
| `tm_follow` | **Yes — FIXED** | Applied to `tm_P_step`; see remaining limitations below |
| `tm_exec` | **Yes** | Auto-peels & simplifies TM steps; replaced all manual step chains |
| `tm_exec` + auto-shift | **Yes** | `shifts [A_shift, C_shift, E_shift]` auto-applies shift lemmas |
| `tm_step`/`tm_steps` | No | Superseded by `tm_exec` for Antihydra |
| `tm_chain` | No | `antihydra_init_loop_start` is already `rfl` |
| `tm_simp` | No | `tm_exec [antihydra, P_Config_Pad]` subsumes this |
| `tm_finish` | No | Not needed |
| `⟪! q \| l \| h \| r ⟫` | No | Left-tape convention mismatch (visual vs zipper) |
| `xs ×× n` | No | Marginal benefit for current proofs |
| `StreamDefs` | **Yes** | Replaces `RightPadEquiv` (~123→59 lines, -64 net) |

---

## Bugs to fix

### 1. `tm_follow` — FIXED, largely superseded by `tm_exec`

**Fixed:** Two bugs corrected:
- `elabTerm h none` → `lctx.findFromUserName?` (resolves local hypotheses)
- `evalNat` → symbolic `omega` (handles variable step counts like `N+4`)

**Superseded:** `tm_exec` now handles the main use case (auto-stepping through
concrete runs). `tm_follow` is still available for chaining named hypotheses but
is no longer needed for the Antihydra proofs.

**Remaining limitations (if using `tm_follow` directly):**
- After a chain of `tm_follow` calls, the remaining step count is a nested
  `Nat.sub` expression that doesn't reduce to 0 by `rfl`.
- Only works on goals of the form `run tm c k = c'`, not `.state = none` goals.
- Config mismatch: if the hypothesis uses `ones 2 ++ ...` but the goal has
  `true :: true :: ...`, `rw` inside `tm_follow` fails.

### 2. `tm_simp` lacks extensibility — partially addressed

**File:** `Tactics.lean:36-44`
**Issue:** `tm_simp` hardcodes its simp set. Every proof file needs a custom wrapper
(`ah_simp` in Antihydra) to include the TM definition and config constructors.
**Partial fix:** `tm_exec [antihydra, P_Config_Pad]` accepts extra simp lemmas,
solving this for multi-step execution. `tm_simp` itself still hardcoded for
single-step use.
**Remaining:** Either make `tm_simp` accept extra lemmas too, or deprecate it
in favor of `tm_exec`.

### 3. Fin literal vs abbreviation mismatch

**File:** `Notation.lean:78-83`
**Issue:** `simp [step, antihydra]` reduces state values to numeric Fin literals
(`5 : Fin 6` via `OfNat`) which don't unify with `stF := ⟨5, by omega⟩`.
**Current workaround:** `simp (config := { decide := true }) [...]`  — already in `tm_simp`.
**Auto-shift fix:** `tm_exec` with `shifts` auto-generates `rw [show (0 : Fin 6) = stA from rfl]`
inside a `conv` block to convert Fin literals to state abbreviations before applying
shift lemmas. This is fully automatic — no manual `show ... from rfl` needed.
**Better fix (not done):** Add simp lemmas `@[simp] lemma stA_eq : (0 : Fin 6) = stA := rfl` etc.

---

## Missing features (architectural)

### 4. Infinite/coinductive tapes — DONE

**Implemented** in `BusyLean/StreamDefs.lean` (~340 lines). Key types/lemmas:
- `Side := Nat → Sym` (infinite half-tape), `SConfig n` (stream-based config)
- `Config.toSConfig`: embedding from finite-list configs to stream configs
- `toSConfig_step`/`toSConfig_run`: commutativity with the embedding
- `toSConfig_padding_indep`: configs differing only in trailing zeros map to same SConfig
- `listToSide`, `Side.blank`, `Side.prepend`, notation `blank∞` and `xs *> s`

**Applied** to Antihydra.lean: replaced the ~123-line `RightPadEquiv` block with ~59
lines of stream-based equivalents (`P_Config_Pad_toSConfig_eq`, `step_left_eq`,
`run_pad_transfer`, `listToSide_blank_of_all_false`, `isValidLoopStart_of_pad_transfer`).
Net savings: ~64 lines.

**Remaining opportunity:** The stream infrastructure could eliminate more boilerplate
if the main proof used `SConfig` directly (instead of bridging back to list configs).
This would require rewriting the shift lemmas and loop proofs to work on `SConfig`,
which is a larger refactor.

### 5. Factored loop lemmas / auto-shift — DONE (Part A)

**BusyCoq:** Factors out repeating loops as separate lemmas (`B_rep`) and uses `ind`
to prove them by induction. The main rules (`R0`, `R1`, `Rhalt`) are ~10 lines each.

**BusyLean/Antihydra:** Now uses `tm_exec [...] shifts [...]` for automatic shift
lemma application. When `tm_exec` gets stuck on a step that can't be simplified,
it tries each shift lemma:

1. Extracts `ones k` prefix from the config's tape (left or right)
2. Resolves shift lemma names and extracts the target state abbreviation
3. Computes `rest = stepCount - (k + 1)` cleanly via `computeShiftRest`
   (decomposes additive terms, avoids `Nat.sub`)
4. Splits with `run_add`, rewrites Fin→abbreviation via `conv`, applies shift
5. Resumes concrete stepping

**Results on Antihydra macro theorems:**
| Theorem | Before auto-shift | After | Savings |
|---------|-------------------|-------|---------|
| `tm_P_step` | 8 lines | 1 line | -7 |
| `tm_odd_endgame` | 15 lines | 4 lines | -11 |
| `tm_odd_halt_endgame` | 11 lines | 4 lines | -7 |
| `tm_even_endgame_to_loop` | 38 lines | 22 lines | -16 |

**Implementation:** ~120 new lines in Tactics.lean:
- `computeShiftRest`, `collectAddTerms`, `extractCoeff`, `buildSum` — clean step
  count arithmetic for multi-variable expressions (e.g., `3*N + 2*b + 24`)
- `getShiftStateAbbrev` — extracts state abbreviation from shift lemma type
  (manual binder stripping, no `forallTelescope` to avoid fvar leaks)
- `extractOnesPrefix` — finds `k` in `ones k ++ R` (handles abbrev, whnf, replicate)
- `tryApplyShift` — core shift application logic with `conv`-isolated Fin rewriting

**Remaining limitations:**
- `cases` splits (structural, not a shift issue) — must be done manually
- Tape where `ones k` isn't syntactically at the list head (e.g., bare `ones b'`
  without `++ R`) — needs manual `rw [show ones b' = ones b' ++ [] ...]` first
- Post-shift final config cleanup (folding `true :: true :: ... :: ones N` into
  `ones (N+6)` and matching `P_Config_Pad`) requires manual `simp + congr + omega`
- fvar leak in certain scopes — auto-shift can't be used directly after `conv`-based
  manual shifts in some `cases` branches (workaround: do one manual shift first)

**Part B: Padding transfer helpers — DONE**
Two helpers (`pad_transfer_loop`, `pad_transfer_halt`) factor out the repeated
`P_Config_Pad_toSConfig_eq` → `run_pad_transfer` → extract pattern from the 3
bridge lemmas (`tm_even_full`, `tm_odd_halt_ex`, `tm_odd_continue`). Each bridge
lemma now ends with a 1-2 line call to the helper instead of ~10 lines of boilerplate.

**Part C (not done): `ind`-like tactic**
For full BusyCoq parity, would need a tactic that chains a base case + inductive
step lemma automatically. This would enable the BusyCoq-style concise rule proofs
(`R0`, `R1`, `Rhalt` as ~10 lines each).

### 6. `es` equivalent (multi-step concrete solver) — DONE

**BusyCoq:** `es` (execute-simplify) runs concrete steps and simplifies automatically.
`do 9 step` runs exactly 9 concrete steps. These are the workhorses.

**BusyLean:** `tm_exec [lemmas]` implemented in Tactics.lean. Repeatedly peels one
TM step via `conv => lhs; enter [2]; simp [run, step, ...]`, folds cons chains
back into `ones`/`zeros` form, and closes with `rfl` when done. Stops when stuck
(shift lemma needed). With `shifts [...]`, auto-applies shift lemmas.

**Applied to:** All 4 macro theorems in Antihydra.lean.

### 7. `listHead`/`listTail` auto-simplification after shift lemmas — DONE

**Issue:** Every shift lemma application used to require:
```lean
have hp_head : listHead (false :: zeros p) false = false := rfl
have hp_tail : listTail (false :: zeros p) = zeros p := rfl
rw [hp_head, hp_tail] at hE; exact hE
```

**Fix:** `tm_exec` with `shifts` includes `listHead, listTail, zeros_succ, ones_succ`
etc. in its conv simp set, handling this automatically.

### 8. Step count arithmetic (`show ... from by omega`) — DONE

**Issue:** Every theorem needed manual omega decomposition of the total step count.

**Fix:** `tm_exec` handles step-count decrement automatically for concrete steps.
Auto-shift computes clean rest expressions via `computeShiftRest` for shift
splits (e.g., `3*N + 2*b + 24 → 2*N + 2*b + 23` after subtracting `N + 1`).
Manual `rw [show ... from by omega]` is still needed for edge cases (e.g., after
`cases b` splits, or for `run_add` splits before manual shift applications).

---

## Priority order

1. ~~**Fix `tm_follow`**~~ — **Superseded by `tm_exec`** (saved ~229 lines)
2. ~~**Infinite tapes**~~ — **DONE** (saved ~64 lines via StreamDefs.lean)
3. ~~**`tm_simp` extensibility**~~ — **Partially addressed** by `tm_exec [lemmas]`
4. ~~**`listHead`/`listTail` auto-cleanup**~~ — **DONE** (handled by auto-shift)
5. ~~**Factored loop support / auto-shift**~~ — **DONE** (Part A: -38 lines in Antihydra)
6. ~~**`es` equivalent**~~ — **DONE** (`tm_exec`)
7. ~~**Padding transfer helpers**~~ — **DONE** (saved ~16 lines in bridge lemmas)
8. **`ind`-like tactic** — largest remaining gap vs BusyCoq (not done)

---

## What a fully optimized Antihydra.lean would look like

**Current state with auto-shift + padding transfer** (~685 lines, down from ~937 originally):
```lean
-- tm_P_step: 1 line (was 44 originally, 8 before auto-shift)
theorem tm_P_step ... := by
  tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]

-- tm_odd_endgame: 4 lines (was 15 before auto-shift)
theorem tm_odd_endgame ... := by
  tm_exec [antihydra, P_Config_Pad] shifts [A_shift, C_shift, E_shift]
  simp only [ones_cons_append]
  congr 1; unfold ones repeatSym; congr 1; omega
```

**Remaining gap vs BusyCoq (~100 lines):**
The ~600 non-macro lines are mostly shift lemma definitions, `P_Config_Pad`,
helper lemmas, the stream-based padding equivalence, bridge lemmas, and the
main induction (`tm_P_multistep`, `tm_simulates_math`). With an `ind` tactic
(item 8), potentially ~550-600 lines.
