# BusyLean TODO

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

### 12. `tm_es` tactic (exhaustive search for →\* goals)

BusyCoq's `es` tactic automatically proves `A →* B` for concrete-prefix
configurations by searching for a small `k` such that `run tm A k = B`. This
is the workhorse for atomic lemmas (Inc1, Inc2, Inc3, LOv1, Ov2, Ov3 — each
~4–8 TM steps).

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

### 4. Prove `matchingConfig?_correct` (backward reasoning completeness)

The core completeness lemma in `BackwardReasoning.lean` has a sorry. Needs case
analysis on direction (R/L) and tape structure (cons/nil) to show that reversing
a step produces a SymConfig matching the predecessor. ~50 lines of proof.

### ~~5. Redefine `zebra` via `listRepeat`~~ ✅ DONE (via item 14)

### 6. `tm_simp` extensibility

`tm_simp` hardcodes its simp set. Either make it accept extra lemmas or deprecate
in favor of `tm_exec`.

### 7. Fin literal simp lemmas

Add `@[simp] lemma stA_eq : (0 : Fin 6) = stA := rfl` etc. to eliminate the
Fin literal vs abbreviation mismatch without needing `simp (config := { decide := true })`.

### 8. `tm_follow` remaining limitations

- **mdata bug**: `have h := thm` wraps the type in `mdata`, so `tm_follow h`
  fails with "not an equality". Root cause: `lctx.findFromUserName?` returns
  the mdata-wrapped type; fix needs `consumeMData` before parsing. Same bug
  existed in `evstep_follow` and was fixed there.
- Nested `Nat.sub` step counts after chaining don't reduce to 0 by `rfl`
- Only works on `run tm c k = c'` goals, not `.state = none`
- Config mismatch when hypothesis uses `ones 2 ++ ...` but goal has `true :: true :: ...`

Mostly superseded by `tm_exec`, but worth fixing if `tm_follow` remains in the API.
**Note:** item 11 (`evstep_follow`) addresses the →\* gap separately.

### 9. `tm_exec` auto-shift limitations

- `cases` splits must be done manually before auto-shift
- Bare `ones b'` without `++ R` needs manual rewrite to `ones b' ++ []`
- Post-shift cleanup (folding cons chains into `ones (N+k)`) sometimes needs manual `congr + omega`
- fvar leak after `conv`-based manual shifts in some `cases` branches

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
