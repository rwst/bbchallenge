# BusyLean TODO

## Open items

### 1. `Trans` instances for Multistep

Enable `calc` chaining with `-[tm]{k}->` notation:
```lean
instance : Trans (Multistep tm j) (Multistep tm k) (Multistep tm (j+k))
```
This would allow `calc A -[tm]{j}-> B; _ -[tm]{k}-> C` syntax.

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

### 5. Redefine `zebra` via `listRepeat`

`zebra c = [false, true] ×× c` with simp lemmas. Cleaner than hand-rolled
recursion, and `listRepeat_concat_comm` helps inductive proofs over zebra patterns.

### 6. `tm_simp` extensibility

`tm_simp` hardcodes its simp set. Either make it accept extra lemmas or deprecate
in favor of `tm_exec`.

### 7. Fin literal simp lemmas

Add `@[simp] lemma stA_eq : (0 : Fin 6) = stA := rfl` etc. to eliminate the
Fin literal vs abbreviation mismatch without needing `simp (config := { decide := true })`.

### 8. `tm_follow` remaining limitations

- Nested `Nat.sub` step counts after chaining don't reduce to 0 by `rfl`
- Only works on `run tm c k = c'` goals, not `.state = none`
- Config mismatch when hypothesis uses `ones 2 ++ ...` but goal has `true :: true :: ...`

Mostly superseded by `tm_exec`, but worth fixing if `tm_follow` remains in the API.

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
