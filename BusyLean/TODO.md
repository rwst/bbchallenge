# BusyLean TODO

## Generic tape identities upstreamed from BMO1 (2026-04-20)

Three pure tape identities were moved from `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE/machine.lean` into the library:

- **`zebra_succ_append (b) : zebra (b+1) = zebra b ++ [false, true]`** — `TapeHelpers.lean`.
  Dual of `zebra_succ`; appends `[false, true]` to the *end* of `zebra b`.
- **`Side.cons_false_blank : cons false blank = blank`** — `StreamDefs.lean` (`@[simp]`).
  Corollary of `prepend_zeros_blank 1`. Triggers automatically via simp wherever a TM
  writes a `0` at the blank boundary.
- **`Side.cons_false_zebra_blank_tail (k)`** — `StreamDefs.lean`.
  Closes both `k = 0` (blank absorption) and `k ≥ 1` (zebra structure) cases uniformly.

### Deferred: `rev_zebra` — stays downstream for now

`rev_zebra` (the `(10)^n` dual of `zebra`) is still defined in BMO1's `machine.lean`.
Per `CLAUDE.md:225-227`, it is documented as the canonical example of a
*machine-specific atom* extending `tape_norm`. Only one TM currently uses it, and
the BMO1-specific bridge lemmas (`ones1_zebra_false_eq_rev_zebra`, `_full_left_list_eq`,
`_right_pattern_eq`) are niche.

**Upstream trigger**: when a second TM proof needs `rev_zebra`, move the bare def +
`rev_zebra_zero_simp` + `rev_zebra_succ_append` to `TapeHelpers.lean`. The `PLAN.md`
sketches (`rev_zebra_add`, `rev_zebra_cons`) remain aspirational until then.

## High-priority: infrastructure for mxdys-style proofs

The mxdys Coq proof of `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` revealed
fundamental gaps in BusyLean's tactic/chaining infrastructure. The Coq proof
uses BusyCoq's `follow`/`finish`/`es`/`ind` to chain many small `→*` steps;
BusyLean currently only supports `run`-equality goals (known step counts).
These gaps forced the Lean proof into an inferior architecture (large concrete
shifts via `native_decide` instead of small inductive steps).

### ~~10. `Trans` instance for `EvStep` (→\* calc chaining)~~ ✅ DONE

Added 7 `Trans` instances in `Multistep.lean`:
- `EvStep`↔`EvStep`, `Multistep`↔`EvStep`, `Multistep`↔`Multistep`, `Progress`↔`EvStep`

Enables `calc`-style chaining:
```lean
calc S1 (n+a) b (n*2+c)
    _ -[tm]->* S1 a (n*3+b) c     := Incs1 n a b c
    _ -[tm]{k}-> S1 ...            := by decide   -- mixed Multistep→EvStep
    _ -[tm]->* ...                 := Ov3 ...
```

### ~~11. `evstep_follow` / `evstep_finish` tactics~~ ✅ DONE

Added in `Tactics.lean`:

**`evstep_follow h`**: Accepts `EvStep`, `Multistep`, or `run` equality
hypotheses. Lifts to `EvStep.trans` and leaves the continuation as the new goal.
Strips `mdata` wrappers (from `have`/`show`).

**`evstep_finish`**: Closes `A →* B` by `EvStep.refl` (definitional equality)
or `⟨0, closeConfigEq_⟩` (congr+omega on struct fields).

**`closeConfigEq_`**: Helper tactic closing `A = B` for Config structs via
nested `congr 1 <;> (rfl | omega)`.

Example:
```lean
theorem IncsOv3 (a b : ℕ) : S3 a b -[tm]->* S1 0 2 (2+a*2+b) := by
  evstep_follow (Incs3 a b)
  evstep_follow (Ov3 (a*2+b))
  evstep_finish
```

### ~~12. `es` / `esx` tactics~~ ✅ DONE (see `BusyLean/EsTactic.lean`, `BusyLean/PLAN.md`)

`es tm [shifts]` proves `A -[tm]->* B` by batching concrete steps via `Meta.reduce`
and applying shift rules by fresh-metavariable unification. `esx tm [shifts]`
proves `∃ k, (run tm A k).halted` via `halts_of_evstep_halted` + the es loop.

Includes:
- `tape_norm` simp set (fold cons prefixes back into atoms: `ones k`, `zebra k`, …)
- 4-level congr/omega cascade in `esFinish` for Nat-index mismatches
- `esx` halt detection via `isHaltedConfig` check on the reduced source

Known limitation: tape-aware shift unification (`tape_unify` in the plan) is
deferred. For cases needing multi-atom context (`rev_zebra k ++ ones 2 ++ L`),
provide parameterized shift variants (e.g. `cd_retreat_ev_left`) rather than
expecting `es` to split the tape automatically.

### 12a. (legacy) `tm_es` — superseded by item 12 above.

**Proposed `tm_es` for BusyLean:**

Given a goal `A -[tm]->* B` where A and B have parameterized tails (e.g.,
`ones k ++ R` for free `k`, `R`):

1. Identify the fixed prefix of each tape (up to the first free variable).
2. Construct a "base" config with only the fixed prefix.
3. Search `k = 1, 2, ..., N` (default N=20) for `run tm base k = base'`
   where `base'` matches the target's fixed prefix.
4. Verify the base run by `decide`.
5. Lift to the full config via `run_right_append` / `run_left_append`.
6. Wrap in `EvStep.from_multistep`.

This combines the existing locality-lifting pattern (used in `launch_rule`,
`shift_4_16`) into a single tactic call. The key insight: with state-C
observation points, every atomic rule touches only a bounded tape region,
so the base configs are small and `decide` is fast.

Stretch goal: also handle `→+` (Progress) goals by additionally checking
the target is not halted.

### 13. Iterated `→*` application (`evstep_ind` or manual pattern)

BusyCoq's `ind n lemma` applies a `→*` lemma `n` times by induction:
```coq
Lemma Incs1 n a b c:
  S1 (n+a) b (n*2+c) →* S1 a (n*3+b) c.
Proof. gen a b c. ind n Inc1. Qed.
```

In Lean, the manual pattern is:
```lean
theorem Incs1 (n a b c : ℕ) :
    S1 (n + a) b (n * 2 + c) -[tm]->* S1 a (n * 3 + b) c := by
  induction n generalizing a b c with
  | zero => simp; exact EvStep.refl
  | succ n ih =>
    calc S1 (n + 1 + a) b ((n + 1) * 2 + c)
        _ -[tm]->* S1 (n + a) (3 + b) (n * 2 + c) := Inc1 (n + a) b (n * 2 + c)
        _ -[tm]->* S1 a (n * 3 + (3 + b)) c       := ih a (3 + b) c
        _ = S1 a ((n + 1) * 3 + b) c               := by ring_nf
```

This pattern requires item 10 (`Trans` for EvStep) to work in `calc` blocks.
A dedicated `evstep_ind` tactic could automate the boilerplate (induction +
arithmetic normalization), but the manual pattern with `calc` + `Trans` is
already usable and more transparent.

**Decision: items 10–11 done; 12 deferred; `evstep_ind` deferred (manual `calc` suffices).**

### ~~14. `zebra` via `listRepeat`~~ ✅ DONE

Added `def zebra : Nat → List Sym` in `TapeHelpers.lean` with direct recursion
(avoids import cycle with `Notation.lean`). Simp lemmas: `zebra_zero`,
`zebra_succ`, `zebra_length`, `zebra_append`.

Bridge lemma `zebra_eq_listRepeat` deferred — direct recursion is cleaner
for the current use case.

### ~~15. Config constructor from full tape list~~ ✅ DONE

Added `mkConfigFromTape` in `Notation.lean` with simp lemmas for `_cons`,
`_nil`, `_state`, `_left`, `_halted`. Enables clean S1/S2/S3 definitions:
```lean
def S1 (a b c : ℕ) : Config 6 :=
  mkConfigFromTape 6 stC (ones (1 + a * 2)) (zebra b ++ ones (c * 2) ++ [false, true])
```

---

## Existing items

### ~~1. `Trans` instances for Multistep~~ ✅ DONE (via item 10)

All `Trans` instances (`Multistep`, `EvStep`, `Progress`, mixed) added in
`Multistep.lean`.

### 2. Convert Antihydra to `closed_set`

Test whether `ClosedSet` simplifies the Antihydra proof vs the current
`nonhalt_of_progress` approach. Measure line savings.

### 3. `TM.haltingPairs` computable list

Add a computable list of halting (state, symbol) pairs to enable `decide`-based
proofs that a specific pair is unreachable within a bounded prefix.

### ~~4. Prove `matchingConfig?_correct` (backward reasoning completeness)~~ ✅ DONE

Complete proof in `BackwardReasoning.lean` — case analysis on direction (R/L)
and tape structure (cons/nil), ~95 lines.

### ~~5. Redefine `zebra` via `listRepeat`~~ ✅ DONE (via item 14)

### 6. `tm_simp` extensibility

`tm_simp` hardcodes its simp set. Either make it accept extra lemmas or deprecate
in favor of `tm_exec`.

### ~~7. Fin literal simp lemmas~~ ✅ DONE

Added `@[simp] theorem stA_val .. stF_val` in `Notation.lean`. Eliminates
`show (2 : Fin 6) = stC from rfl` workarounds (verified: Antihydra Fin rewrites removed).

### ~~8. `tm_follow` remaining limitations~~ ✅ MOSTLY DONE

Fixed:
- **mdata bug**: Switched from `lctx.findFromUserName?` to `Term.elabTerm` +
  `inferType` + `consumeMData` (same approach as `evstep_follow`). Now accepts
  have-bound hypotheses and direct theorem references.
- **Implicit n parameter**: `findRunExpr` now uses `isAppOf` + `getAppArgs`
  instead of 3-level pattern match, handling the implicit `{n : Nat}` in `run`.
- **`.state = none` goals**: `findRunExpr` searches inside accessor applications
  (e.g., `(run tm c k).state`), not just direct `run` expressions.
- **Auto-close**: Added `congr 1 <;> omega` cascade for Nat mismatches after
  `run_zero` reduction. Now `tm_follow` accepts `term` (not just `ident`).

Remaining:
- Config mismatch when hypothesis uses `ones 2 ++ ...` but goal has
  `true :: true :: ...` — would need `tape_norm` normalization before rewrite.

### 9. `tm_exec` auto-shift limitations

- `cases` splits must be done manually before auto-shift
- Bare `ones b'` without `++ R` needs manual rewrite to `ones b' ++ []`
- Post-shift cleanup (folding cons chains into `ones (N+k)`) sometimes needs manual `congr + omega`
- fvar leak after `conv`-based manual shifts in some `cases` branches

---

## Lessons from Antihydra refactoring (2026-04-16)

Refactoring the Antihydra proof (`1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`) against
current BusyLean revealed these gaps and improvements:

### ~~16. `SEvStep` — stream-config EvStep~~ ✅ DONE

Added `SEvStep`, `SEvStep.refl`, `SEvStep.trans`, `SEvStep.from_run`,
`SEvStep.halted_state`, and `Trans` instance in `StreamDefs.lean`.
Notation: `A -s[tm]->* B`.

Enables cleaner backward proofs in halting-equivalence theorems (chain
`SEvStep.from_run h_sim` with `⟨k', rfl⟩` instead of manual `srun_add` rewriting).

### 17. `SProgress` — stream-config Progress

Antihydra's bridge lemmas prove `∃ k, k > 0 ∧ srun tm A k = B` (the `k > 0` is
needed for strong induction in the halt equivalence). This is conceptually
`SProgress` but currently requires manual step-count computation. Adding:
```lean
def SProgress (tm : TM n) (A B : SConfig n) : Prop :=
  ∃ k, 0 < k ∧ srun tm A k = B ∧ B.state ≠ none
```
with `Trans` instances would let bridge lemmas chain via `calc` and eliminate the
manual polynomial step-count arithmetic (`n*(3*n+9) + (9*n+2*b+26)` etc.).

### ~~18. `closeConfigEq_` vs endgame tape folding~~ ✅ DONE

Added 3-deep congr cascade with `tape_norm`+`ones`/`repeatSym` unfolding as
a new level in `closeConfigEq_`. Handles `ones (N+1+1+...) ++ X = ones (N+k) ++ X`
patterns. Antihydra endgames now use `closeConfigEq_` directly instead of the
manual `simp; congr; unfold; congr; omega` pattern.

### 19. SConfig lifting boilerplate

Every Antihydra SConfig theorem follows the same 2-line pattern:
```lean
rw [← P_Config_Pad_toSP ..., ← P_Config_Pad_toSP ..., ← toSConfig_run]
exact congrArg Config.toSConfig (tm_foo ...)
```
A generic tactic `lift_to_sconfig tm pad_bridge` that matches `srun tm A k = B`
goals and rewrites via a padding-bridge lemma would eliminate this repetition.

### ~~20. Fin literal `simp` lemmas (reinforces item 7)~~ ✅ DONE (via item 7)

### 21. `tm_exec` post-shift tape normalization

After `tm_exec` completes, Config fields often have the form
`ones (N+1+1+1+1+1+1) ++ [false] ++ ones b'` instead of the target
`ones (N+6) ++ [false] ++ ones b'`. The `tape_norm` simp set handles the cons
folding but not the final Nat mismatch inside `ones`. Integrating `closeConfigEq_`
into `tm_exec`'s post-loop was attempted but compound tactic state management
(simp+congr cascades under `<;>`) causes partial goal modification that breaks
subsequent standalone `closeConfigEq_` calls. Workaround: use `closeConfigEq_`
as a standalone tactic after `tm_exec`.

---

## Not ported from busybeaver (and why)

| busybeaver feature | Reason |
|---|---|
| `Turing.Tape` / `ListBlank` | Heavyweight mathlib dependency; our zipper model enables fast `decide` |
| `HaltM` monad | Oriented toward automated deciders, not manual proofs |
| NGramCPS decider | Automated technique, not useful for BB(6) holdouts |
| Cycler/loop detection | Same — automated |
| ~~Backward reasoning~~ | **Ported** — `BackwardReasoning.lean` (1 sorry in `matchingConfig?_correct`) |
| Machine enumeration | Not relevant to individual machine proofs |
| `GMachine` typeclass | Over-abstraction for our use case |
