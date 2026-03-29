# BusyLean TODO: Lessons from Antihydra + BusyCoq Comparison

## Current state

BusyCoq AntiHydra.v: ~100 lines (Coq)
Antihydra.lean: ~937 lines (Lean, after applying all available BusyLean optimizations)

The ~9x gap is explained by both missing BusyLean features and fundamental
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
| `tm_step`/`tm_steps` | No | `ah_simp` used instead; untested interaction with variable-length runs |
| `tm_chain` | No | `antihydra_init_loop_start` is already `rfl` |
| `tm_simp` | No | Custom `ah_simp` used (needs `antihydra`, `P_Config_Pad`) |
| `tm_finish` | No | Not needed |
| `⟪! q \| l \| h \| r ⟫` | No | Left-tape convention mismatch (visual vs zipper) |
| `xs ×× n` | No | Marginal benefit for current proofs |
| `StreamDefs` | **Yes** | Replaces `RightPadEquiv` (~123→59 lines, -64 net) |

---

## Bugs to fix

### 1. `tm_follow` — FIXED, remaining limitations

**Fixed:** Two bugs corrected:
- `elabTerm h none` → `lctx.findFromUserName?` (resolves local hypotheses)
- `evalNat` → symbolic `omega` (handles variable step counts like `N+4`)

**Remaining limitations:**
- After a chain of `tm_follow` calls, the remaining step count is a nested
  `Nat.sub` expression (e.g., `2*n+12 - 1 - 1 - (n+1) - ...`) that doesn't
  reduce to 0 by `rfl`. Closing the proof requires:
  `simp only [show <remaining> = 0 from by omega]; simp [run, ...]`
- Only works on goals of the form `run tm c k = c'`, not `.state = none` goals.
  Theorems proving halting (like `tm_odd_halt_endgame`) can't use `tm_follow`.
- Config mismatch: if the hypothesis uses `ones 2 ++ ...` but the goal has
  `true :: true :: ...`, `rw` inside `tm_follow` fails. Need manual `rw [h_eq]`
  normalization on the hypothesis first.

**Applied to:** `tm_P_step` in Antihydra.lean (saves 2 lines + omega decomposition).

### 2. `tm_simp` lacks extensibility

**File:** `Tactics.lean:36-44`
**Bug:** `tm_simp` hardcodes its simp set. Every proof file needs a custom wrapper
(`ah_simp` in Antihydra) to include the TM definition and config constructors.
**Fix:** Either:
- (a) Provide a `tm_simp` variant that accepts extra simp lemmas: `tm_simp [antihydra, P_Config_Pad]`
- (b) Use a scoped simp extension / attribute that proof files can add to

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

### 6. `es` equivalent (multi-step concrete solver)

**BusyCoq:** `es` (execute-simplify) runs concrete steps and simplifies automatically.
`do 9 step` runs exactly 9 concrete steps. These are the workhorses.

**BusyLean:** `tm_steps n` exists but was never tested on Antihydra. `tm_step` uses
`rw [run_peel ...]` + `simp only [step, run]; tm_simp` which may be slow for large n.

**Fix:** Test `tm_steps` on real proofs. Consider a faster implementation that
batches steps (like `tm_chain` but for producing intermediate have-lemmas rather
than closing the goal).

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

### 8. Step count arithmetic (`show ... from by omega`)

**Issue:** Every theorem needs a manual omega decomposition of the total step count:
```lean
rw [show 3*N + 20 = 1 + (1 + ((N+1) + ...)) from by omega]
```
This is error-prone and verbose.

**Fix:** If `tm_follow` worked, this would be automatic (each `tm_follow` call
does its own omega internally). Fixing `tm_follow` (item 1) eliminates this
entirely.

---

## Priority order

1. **Fix `tm_follow`** — unblocks the biggest line savings (~2 lines saved per step
   lemma application, ~40+ lines per theorem)
2. ~~**Infinite tapes**~~ — **DONE** (saved ~64 lines in Antihydra via StreamDefs.lean)
3. **`tm_simp` extensibility** — eliminates need for per-file `ah_simp` wrappers
4. **`listHead`/`listTail` auto-cleanup** — saves 3 lines per shift lemma use
5. **Factored loop support / `ind`** — enables BusyCoq-style concise rule proofs
6. **Test `tm_steps`** — verify it works on real proofs, optimize if slow

---

## What a fully optimized Antihydra.lean would look like

With items 1, 3-4 fixed (item 2/infinite tapes already done), the core theorems would shrink from:

```lean
-- Current: ~30 lines per theorem
theorem tm_P_step ... := by
  have step1 : run ... 1 = ... := by ah_simp
  have step2 : run ... 1 = ... := by ah_simp
  ...
  have step11 : run ... 1 = ... := by ah_simp
  rw [show 2*n+12 = 1+(1+(...)) from by omega]
  rw [run_add, step1, run_add, step2, ...]
  simp [P_Config_Pad]
```

To:

```lean
-- With tm_follow fixed: ~15 lines
theorem tm_P_step ... := by
  have step1 : ... := by tm_step
  ...
  tm_follow step1; tm_follow step2; ...
  simp [P_Config_Pad]
```

With items 1, 3-5 all fixed (infinite tapes already done + factored loops), the
entire file could potentially reach ~200-300 lines, comparable to BusyCoq's structure.
