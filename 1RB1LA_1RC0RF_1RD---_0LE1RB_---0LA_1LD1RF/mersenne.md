# Mersenne preservation: plan and progress

## Current state

4 sorries in `machine_base.lean` for "Mersenne preservation" conditions:

| # | Theorem | Line | Output | Sorry goal |
|---|---------|------|--------|-----------|
| 1 | `invariant_sweep_and_shift` | 1374 | `M L (a+1) (1::(d+1)::R)` | `L=[] → ¬IsMersenne(a+1)` |
| 2 | `invariant_zero_bounce_and_shift` | 1391 | `M L (a+4) [1,1]` | `L=[] → ¬IsMersenne(a+4)` |
| 3 | `invariant_zero_two_solo` | 1398 | `M L (a+3) [1]` | `L=[] → ¬IsMersenne(a+3)` |
| 4 | `invariant_zero_two` | 1424 | `M L (a+3) ((d+1)::R)` | `L=[] → ¬IsMersenne(a+3)` |

The invariant condition `L = [] → ¬IsMersenne c` was added to `M_Config` to prevent halting. Each of these 4 theorems produces an M_Config output with L = input_tail (possibly empty). When L_output = [], we need to show the cursor is non-Mersenne.

## Key math: `not_mersenne_of_half`

```
c ≥ 3 ∧ c odd ∧ ¬IsMersenne c → ¬IsMersenne ((c-1)/2)
```

This lemma (already proven in machine_base.lean) says non-Mersenne is closed under the `(c-1)/2` iteration. This is the key to the sweep cascade preservation.

## Needed invariant strengthening

### M_Config: track single-L Mersenne-avoidance at odd c

Add to M_Config invariant:
```
∀ a, L = [a] → c % 2 = 1 → c ≥ 3 → ¬IsMersenne (a + c/2)
```

Where `a + c/2` is the cursor value that would result from sweeping [a] down to c=1 and then shifting.

**Preservation check for sweep (odd c, c' = c-2):**
- Input: L=[a], c=2k+1. Condition: `a+k not Mersenne`.
- Sweep output: L=[a+1], c=2k-1. Condition: `(a+1) + (k-1) = a+k not Mersenne`. ✓ Same value, preserved.

**Preservation for sweep_and_shift (c=3, L=[a]):**
- Input condition: `a+1 not Mersenne`.
- Output: M([], a+1, ...). Output L=[], so the existing condition `L=[]→¬IsMersenne c` needs `¬IsMersenne(a+1)`. ✓ Direct match.

**Preservation for sweep_left_empty (input c_in = 2k+1, output L=[1], c_out = 2k-1):**
- Input L=[], Mersenne condition: `¬IsMersenne(2k+1)`.
- Output L=[1], c=2k-1 odd. Need: `1 + (2k-2)/2 = 1 + (k-1) = k not Mersenne`.
- From `¬IsMersenne(2k+1)` apply `not_mersenne_of_half`: `¬IsMersenne((2k+1-1)/2) = ¬IsMersenne(k)`. ✓

### M0_Config: track single-L Mersenne-avoidance for M0→M transitions

Add to M0 invariant:
```
∀ a, L = [a] → ¬IsMersenne (a + 3) ∧ ¬IsMersenne (a + 4)
```

This directly provides what's needed for:
- `invariant_zero_two_solo` (output c = a+3)
- `invariant_zero_two` (output c = a+3)
- `invariant_zero_bounce_and_shift` (output c = a+4)

**Preservation check for M0 single-L producers:**
- `sweep_to_zero_left_empty`: always produces L=[1]. 1+3=4, 1+4=5. Neither Mersenne. ✓
- `sweep_to_zero` with M input having single L=[b]: output L=[b+1]. Need b+4, b+5 not Mersenne.
  - Input M([b], 2, d::R): c=2 even. The new M_Config condition `c odd → ...` is vacuous at c=2.
  - But b+4, b+5 could be Mersenne if b=3 (b+4=7) or b=2 (b+5=7).
  - From M_Config invariant with L=[b] at c=2: need additional condition.

Hmm, this cascades: sweep_to_zero from M([b], 2, ...) needs to ensure output M0([b+1], ...) has b+1+3, b+1+4 non-Mersenne.

So the M_Config invariant at even c also needs tracking, or we need to rule out certain b values at c=2.

### Cascade analysis: where does single-L M arise at c=2?

From sweep at c=4 single-L: M([b-1], 4, d::R) → M([b], 2, (d+1)::R). Input single-L at c=4.
From sweep_left_empty at c=4: M([], 4, d::R) → M([1], 2, (d+1)::R). Output L=[1], b=1. 1+4=5, 1+5=6. Both not Mersenne. ✓

So if input is single-L M([b], 4, ...), we need another condition on b. This cascades to c=6, c=8, etc.

At even c=2k, single-L [b] came from M([b-k+1], 2k, ...) originally, ultimately from M([], 2k, ...) or sweep_left_empty from c=2k+2.

Let me check each initial value:
- M([], 4, R) → M([1], 2, R'). b=1. 1+4=5, 1+5=6. Not Mersenne. ✓
- M([], 6, R) → M([1], 4, R') → M([2], 2, R''). b=2. 2+4=6, 2+5=7. **7 IS Mersenne**! BAD.
- M([], 8, R) → M([3], 2, R'). b=3. 3+4=7. BAD.
- M([], 10, R) → M([4], 2, R'). b=4. 4+4=8, 4+5=9. Not Mersenne. ✓
- M([], 12, R) → M([5], 2, R'). b=5. 5+4=9, 5+5=10. Not Mersenne. ✓
- M([], 14, R) → M([6], 2, R'). b=6. 6+4=10, 6+5=11. Not Mersenne. ✓

So M([], 6, R) and M([], 8, R) give bad b values at c=2!

But wait: simulation never shows M([], 6, R) or M([], 8, R) with R nonempty at the reachable set. Let me check.

From earlier sim: L=[] c values with R nonempty: {2, 4, 5, 6, 11, 13, 18, 24, 27, ...}.

**c=6 IS in the reachable set!** Specifically M([], 6, [1,7,14,2]) at step 1566 (from era_study.py).

And M([], 6, R) → sweep_left_empty → M([1], 4, R') → sweep → M([2], 2, R'').

M([2], 2, R''): zero_two produces M0([3], (R''[0]+1)::R''[1:]). Check: M0([3], ...). 3+3=6, 3+4=7. **7 IS Mersenne**!

So if the M0 output R starts with 2, zero_two fires and gives M([], 3+3-2=4+2=6, ...)? Let me re-check.

Actually `zero_two_solo` fires when R=[2], producing M(L', a+3, [1]). With single-L M0([3], [2]), output M([], 6, [1]). c=6, L=[]. Need ¬IsMersenne(6). 6 is not Mersenne ✓.

But we also need to check zero_two (multi R). M0([3], 2::d::R): output M([], 6, (d+1)::R). c=6, L=[]. ¬IsMersenne(6) ✓.

So output c=6 is fine. The issue is: the M0 invariant condition `a+3 not Mersenne, a+4 not Mersenne` for single-L M0([3], ...) requires 3+3=6 (OK) and 3+4=7 (Mersenne, BAD).

So the M0 single-L with a=3 ***would violate*** the a+4 condition. This means the M0([3], [4]) case would produce a Mersenne output via zero_bounce_and_shift.

Check: M0([3], [4]): zero_bounce_and_shift → M([], 3+4=7, [1,1]). c=7. 7 IS Mersenne. BAD!

So M0([3], [4]) IS a problematic config. Does it arise?

Simulation data: M0 single-L R=[4] count was... let me check. From earlier: `M0([a], [4]) a values: []` — empty! Never appears.

So M0([3], [4]) is unreachable. But the current invariant doesn't exclude it.

## Conclusion: cascade is real and complex

The Mersenne closure via `(c-1)/2` works for the sweep chain (odd c), but the M0→M transitions at zero_two / zero_bounce / etc. cross between odd and even and break the closure.

The "safe set" is irregular and depends on the specific orbit's structure, not a simple arithmetic predicate.

## Pragmatic path forward

**Option A**: Add the strengthened conditions as-is and accept some sub-cases as `sorry`. At least the sweep cascade is closed.

**Option B**: Verify reachable M0 single-L a values by computation. All observed values don't produce Mersennes, but we'd need to prove this for ALL reachable, not just observed.

**Option C**: Track a richer invariant that captures the orbit structure (era boundaries, run-length sums, etc.). This is essentially approach (B) from Basics.lean §10h — era-based predicate.

**Option D**: Accept the 4 Mersenne sorries as "empirically verified reachability assumptions" and document them as axiomatic. The theorem `sweeper_never_halts` would then depend on these 4 assumptions.

## Decision

Going with **Option A**: add the sweep-chain Mersenne tracking to M_Config, which closes sorry #1 (invariant_sweep_and_shift). The other 3 sorries may need Option D (documented assumptions) or more work.

## Implementation steps

1. Add to M_Config invariant: `∀ a, L = [a] ∧ c % 2 = 1 ∧ c ≥ 3 → ¬IsMersenne (a + c/2)`
2. Update all invariant preservation proofs to establish the new field
3. Update `invariant_sweep_and_shift` to use the new field for its sorry
4. For sorries #2, #3, #4: add analogous M0 invariant condition, attempt preservation proofs
5. Document remaining sorries as empirically-verified reachability assumptions
