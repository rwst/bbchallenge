# bb2x5.lean generalizations

Follow-ups identified by comparing `bb2x5.lean` against BusyCoq's
`Individual25.v` and the 2x5 machine proof `1RB0LB2LA4LB3LA_2LA---3RA4RB2RB.v`.

## High value

- [x] **(1) `Progress` + `EvStep` relations with `Trans` instances** ✓
  - `A -[tm]->+ B  :=  ∃ k > 0, run tm A k = B ∧ ¬ B.halted`
  - `A -[tm]->* B  :=  ∃ k, run tm A k = B`
  - `Trans` instances for all pairs among `Multistep`/`Progress`/`EvStep`
  - Unlocks calc chaining à la BusyLean `Multistep.lean:71–100`

- [x] **(2) `progress_nonhalt_simple`** ✓
  - Signature:
    `∀ {C}, (f : C → Config) → (∀ c, ∃ c', f c -[tm]->+ f c') → ∀ c m, ¬ (run tm (f c) m).halted`
  - Ergonomic: user provides a `BigStep`-style enumeration over an abstract
    state type; library handles the induction. Matches BusyCoq's
    `progress_nonhalt_simple` usage in 2x5 proofs.

- [x] **(3) `lpow` (list power) + arithmetic lemmas** ✓
  - `lpow : List Sym → Nat → List Sym` with `_ ++ _` semantics
  - Lemmas: `lpow_zero`, `lpow_succ`, `lpow_add`, `lpow_mul`, `lpow_rotate`,
    `map_lpow`, `lpow_length`
  - Your `rep`/`repPair` become specializations:
    `rep s n = lpow [s] n`, `repPair a b n = lpow [a,b] n`
  - Needed for the repeating 3-cell pattern `[2;2;4]^^n` that Coq uses.

- [x] **(5) `tm!` parser macro** ✓
  - `tm! "1RB---0RB0LA2RA_2LB2LA3RA4LB0LB"` produces the transition function.
  - Mirrors BusyCoq `TM_from_str` (Individual25:368–427) and BusyLean
    `Parser.lean`. Shrinks the 10-case match in `machine.lean` to one line.

## Lower priority / bigger scope

- [ ] **(4) `shift_rule_L` / `shift_rule_R`** (needs `lpow`)
  - Lift a per-block shift into an n-block shift.
  - Backbone for an `es`-style tactic.
  - Matches `Individual25.v:148–184`.

- [ ] **(6) `es` tactic port to 5-symbol**
  - Automate execute + shift-rule alternation (Coq `er`/`sr`/`es`).
  - Substantial work; BusyLean has `EsTactic.lean` for binary as a template.
  - Payoff: 16-state proofs become `destruct x; cbn; es` one-liners.

## Progress log

- (1) Added `Progress` / `EvStep` + `Trans` instances to `bb2x5.lean`
  (post-Multistep, pre-tm_follow section).
- (2) Added `progress_nonhalt_simple` (abstract-state-type wrapper for
  `nonhalt_of_progress`).
- (3) Added generic `lpow` with `lpow_add`, `lpow_mul`, `lpow_length`,
  `map_lpow`, `lpow_rotate`. `rep`/`repPair` now linked via `rep_eq_lpow` /
  `repPair_eq_lpow`. `^^` notation dropped (conflicts with `Bool.xor`).
- (5) Added `parseTM` + `tm!` macro. Verified by a `decide` example in
  `machine.lean` that `tm! "1RB---0RB0LA2RA_2LB2LA3RA4LB0LB"` agrees
  pointwise with the manual `tm` definition.
