# BusyLean TODO: Lessons from Antihydra + BusyCoq Comparison

## Current state

BusyCoq AntiHydra.v: ~100 lines (Coq)
Antihydra.lean: ~716 lines (Lean, after `tm_exec` + StreamDefs optimizations)

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
| `tm_exec` | **Yes** | New tactic: auto-peels & simplifies TM steps; replaced all `ah_simp` chains |
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
(`5 : Fin 6` via `OfNat`) which don't unify with `stF := ���5, by omega⟩`.
**Current workaround:** `simp (config := { decide := true }) [...]`  — already in `tm_simp`.
**Better fix:** Add simp lemmas `@[simp] lemma stA_eq : (0 : Fin 6) = stA := rfl` etc.
or change the abbreviations to use `OfNat` so they're definitionally equal to what
`simp` produces.

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

### 5. Factored loop lemmas / `ind` tactic

**BusyCoq:** Factors out repeating loops as separate lemmas (`B_rep`) and uses `ind`
to prove them by induction. The main rules (`R0`, `R1`, `Rhalt`) are ~10 lines each.

**BusyLean/Antihydra:** Inlines everything. `tm_even_endgame_to_loop` is ~140 lines
because it manually steps through the full B-rep loop. The shift lemmas
(`A_shift`, `C_shift`, `E_shift`) partially address this but are Antihydra-specific
and still require manual `listHead`/`listTail` cleanup after application.

**Fix:**
- Provide a tactic or helper for generating shift/sweep lemmas from a pattern
- Provide an `ind`-like tactic that chains a base case + inductive step lemma
  automatically

### 6. `es` equivalent (multi-step concrete solver) — DONE

**BusyCoq:** `es` (execute-simplify) runs concrete steps and simplifies automatically.
`do 9 step` runs exactly 9 concrete steps. These are the workhorses.

**BusyLean:** `tm_exec [lemmas]` implemented in Tactics.lean. Repeatedly peels one
TM step via `conv => lhs; enter [2]; simp [run, step, ...]`, folds cons chains
back into `ones`/`zeros` form, and closes with `rfl` when done. Stops when stuck
(shift lemma needed). User provides shift lemma applications manually between
`tm_exec` calls.

**Applied to:** All 4 macro theorems in Antihydra.lean. Savings: ~229 lines
(~298 → ~69 lines across `tm_P_step`, `tm_odd_endgame`,
`tm_even_endgame_to_loop`, `tm_odd_halt_endgame`).

### 7. `listHead`/`listTail` auto-simplification after shift lemmas

**Issue:** Every shift lemma application requires:
```lean
have hp_head : listHead (false :: zeros p) false = false := rfl
have hp_tail : listTail (false :: zeros p) = zeros p := rfl
rw [hp_head, hp_tail] at hE; exact hE
```
This is 3 lines of boilerplate per shift lemma use. Using `simp at hE` instead
sometimes over-normalizes (expands `ones n` into cons chains or `List.replicate`).

**Fix:** Either:
- (a) Add a `tm_shift` tactic that applies a shift lemma and auto-eliminates
  `listHead`/`listTail` with targeted simp
- (b) Reformulate shift lemmas to take the head/tail values as explicit arguments
  so the output is already clean
- (c) Add focused simp lemmas: `listHead (x :: _) _ = x` and `listTail (x :: xs) = xs`
  to a controlled simp set that won't over-normalize

### 8. Step count arithmetic (`show ... from by omega`) — partially addressed

**Issue:** Every theorem needs a manual omega decomposition of the total step count.

**Partial fix:** `tm_exec` handles step-count decrement automatically for concrete
steps. Manual `rw [show ... from by omega]` is still needed before shift lemma
applications (to split `run` at the right point via `run_add`), but the per-step
arithmetic is eliminated.

---

## Priority order

1. ~~**Fix `tm_follow`**~~ — **Superseded by `tm_exec`** (saved ~229 lines)
2. ~~**Infinite tapes**~~ — **DONE** (saved ~64 lines via StreamDefs.lean)
3. ~~**`tm_simp` extensibility**~~ — **Partially addressed** by `tm_exec [lemmas]`
4. **`listHead`/`listTail` auto-cleanup** — saves 3 lines per shift lemma use
5. **Factored loop support / `ind`** — enables BusyCoq-style concise rule proofs;
   largest remaining gap vs BusyCoq
6. ~~**`es` equivalent**~~ — **DONE** (`tm_exec`)

---

## What a fully optimized Antihydra.lean would look like

**Current state with `tm_exec`** (~716 lines, down from ~937):
```lean
-- tm_P_step: 7 lines (was 44)
theorem tm_P_step ... := by
  tm_exec [antihydra, P_Config_Pad]       -- concrete steps
  rw [..., run_add]; simp only [A_shift]  -- shift lemma
  tm_exec [antihydra, P_Config_Pad]       -- more concrete steps
  rw [..., run_add]; simp only [C_shift]  -- shift lemma
  tm_exec [antihydra, P_Config_Pad]       -- close
```

**Remaining gap vs BusyCoq (~100 lines):**
The ~600 non-macro lines are mostly shift lemma definitions, `P_Config_Pad`,
helper lemmas, and the stream-based padding equivalence. With factored loop
support (item 5), the file could potentially reach ~300-400 lines.
