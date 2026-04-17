# TM5 Nonhalt Proof — Current Status (2026-04-17)

The file `machine.lean` proves `nonhalt` (the 2-state 5-symbol TM does not halt)
modulo **1 sorry** in `canonical_progress` (line ~1001). The sorry is
**currently unprovable** because the invariant used to justify it is false.
See `strategy.md` for analysis and candidate paths forward.

## Architecture

```
nonhalt
  ├── reaches_canonical        ✓  (native_decide, 117 steps)
  └── canonical_progress       1 sorry
        ├── cycle_nonzero case           ✓
        ├── even overflow case           ✓  (via false parity invariant)
        └── odd overflow case
              ├── k=0            1 sorry  (requires binOdd bin_rest = true)
              ├── k=1            eliminated by false invariant (hbo : binOdd = false)
              ├── k≥2            eliminated by false invariant
              └── all-s3         eliminated by false invariant
```

## Why the remaining sorry is unprovable

`IsCanonical` currently includes field 8:
```
binOdd bin_cells = (ternOdd tern_cells == (pad == 1))
```

This invariant is:
- Preserved by `cycle_nonzero` (both parities flip)
- Preserved by `overflow_cycle` (binOdd flips, ternOdd stays false)
- **NOT preserved by `overflow_odd`**: output is `binOdd bin_rest = true`,
  but simulation shows `bin_rest = 130` (even) occurs at era 1.

See `macro.md` section "Parity of binary at odd overflow" for the data showing
the invariant is false starting at era 1 (T_dig=7, B=130).

## Current IsCanonical fields (8 fields — field 8 is WRONG)

1. `c = CycleStart bin_cells tern_cells pad`
2. `∀ s ∈ bin_cells, s = s2 ∨ s = s3`
3. `ValidTern tern_cells`
4. `pad ≤ 1`
5. `tern_cells.length ≥ 2`
6. `bin_cells ≠ []`
7. `pad = 1 → bin_cells.length ≥ 2`
8. `binOdd bin_cells = (ternOdd tern_cells == (pad == 1))` ← **FALSE at era 1+**

## Completed theorems

- `init_to_cycle`: `native_decide` (117 steps)
- `reaches_canonical`: trivial from `init_to_cycle` + existence of initial canonical
- `cycle_nonzero`: fully proved, preserves all 8 fields (incl. parity flip)
- `overflow_cycle` (even overflow): fully proved, binOdd flips, handles carry_stop + overflow_carry
- `overflow_odd` (odd overflow k=0): proved in 6d+9 steps
- `overflow_odd_k1` (odd overflow k=1): proved in 6d+10 steps

## Missing theorems (would be needed for a correct proof)

- `overflow_odd_k` (general k ≥ 2): complex cascade, not yet proved
- Unreachability of all-s3 at odd overflow (crux of the nonhalting argument)

## Next steps

See `strategy.md` for candidate paths:
1. Remove field 8 and revert to original 4-sorry structure; attack each case
   individually (returns to the plan in `strategy.md`)
2. Replace field 8 with a correct (possibly complex) invariant
3. Use computational verification for a bounded prefix + structural argument
4. Abandon `IsCanonical`-based progress in favor of a different proof skeleton
