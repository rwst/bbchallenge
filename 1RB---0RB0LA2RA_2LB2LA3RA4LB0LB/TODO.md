# TM5 Nonhalt Proof — Remaining Sorries

The file `machine.lean` proves `nonhalt` (the 2-state 5-symbol TM does not halt)
modulo **4 sorries** in `canonical_progress`. The rest compiles cleanly.

## Architecture

```
nonhalt
  ├── reaches_canonical        ✓  (native_decide, 117 steps)
  └── canonical_progress       4 sorries
        ├── cycle_nonzero case     ✓
        ├── even overflow case     1 sorry (carry_stop bin'.length ≥ 2)
        └── odd overflow case      3 sorries
              ├── k=0              ✓  (overflow_odd)
              ├── k=1              sorry (bin_rest.length ≥ 2 for output)
              ├── k≥2              sorry (complex cascade, not yet proved)
              └── all-s3           sorry (must prove unreachable → HALT)
```

## Current approach: binValue tracking

### Phase 1: Infrastructure (~40 lines)
- [ ] Define `binValue : List Sym → Nat` (LSB-first binary value)
- [ ] Define `ternValue : List Sym → Nat` (ternary value from paired cells)
- [ ] Prove `binValue (rep s3 n) = 2^n - 1`
- [ ] Prove `binValue (rep s2 n) = 0`
- [ ] Prove `ternValue (repPair s4 s2 d) = 3^d - 1`

### Phase 2: Conservation + parity (~80 lines)
- [ ] Prove cycle_nonzero conserves `binValue bin + ternValue tern`
- [ ] Add parity invariant to IsCanonical:
      `binOdd bin XOR (ternValue tern % 2 = 0) = (pad = 1)`
- [ ] Prove parity preserved by cycle_nonzero
- [ ] Prove parity preserved by even overflow
- [ ] Prove parity holds for initial config

### Phase 3: All-s3 elimination (sorry 4, ~30 lines)
- [ ] At odd overflow (pad=1, tern=0): invariant → binOdd = false → V even
- [ ] overflow_carry sub-case: V₀=0, V_final = 3^d-1 (even) ≠ 2^n-1 (odd)
- [ ] carry_stop sub-case: V₀ even, V_final = V₀ + 3^d-1 (even) ≠ 2^n-1 (odd)
- [ ] Conclude: bin ≠ rep s3 dd

### Phase 4: Remaining sorries (sorries 1-3)
- [ ] Sorry 1 (even overflow bin'.length ≥ 2): may need parity to invoke hlen2
- [ ] Sorry 2 (k=1 bin_rest.length ≥ 2): needs stronger bin.length invariant
- [ ] Sorry 3 (k≥2): needs general k overflow theorem or separate analysis

## Key insight: parity infinite regress is avoided

Tracking binOdd alone leads to infinite regress (mod 2 needs mod 4 needs mod 8...).
The solution combines two facts:
1. **Parity invariant** in IsCanonical: determines binOdd at overflow points
2. **Conservation law** V + T = const within half-era: determines V_final parity

Together they prove V_final is always even at odd overflow, ruling out all-s3
(which requires odd value 2^n - 1).

## Completed

- `reaches_canonical`: native_decide (117 steps)
- `cycle_nonzero`: fully proved (no parity needed)
- `overflow_cycle`: even overflow with both carry_stop and overflow_carry
- `overflow_odd`: k=0 odd overflow (6d+9 steps)
- `overflow_odd_k1`: k=1 odd overflow (6d+10 steps)
- Parity conditions removed from IsCanonical (were wrong after era 1)
- Case split on bin_decompose at odd overflow

## IsCanonical fields (current, 7 fields)

1. `c = CycleStart bin_cells tern_cells pad`
2. `∀ s ∈ bin_cells, s = s2 ∨ s = s3`
3. `ValidTern tern_cells`
4. `pad ≤ 1`
5. `tern_cells.length ≥ 2`
6. `bin_cells ≠ []`
7. `pad = 1 → bin_cells.length ≥ 2`

Planned addition:
8. Parity invariant (exact form TBD during implementation)
