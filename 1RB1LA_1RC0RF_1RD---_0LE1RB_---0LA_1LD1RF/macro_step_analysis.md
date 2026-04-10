# Macro-Step Function Analysis (2026-04-04)

## Complete macro-step mapping (verified over 200K steps, 0 mismatches)

### From M_Config L c R:

| Condition | Result | Steps | Theorem |
|-----------|--------|-------|---------|
| c ≥ 3, L=a::L', R=d::R' | M(a+1::L', c-2, (d+1)::R') | 2c+7 | `macro_sweep` ✓ |
| c = 2, L=a::L', R=d::R' | M0(a+1::L', (d+1)::R') | 11 | `macro_sweep_to_zero` ✓ |
| c ≥ 3, L=[], R=[] | M([1], c-2, [1]) | 2c+7 | `macro_sweep_solo` ✓ |
| c = 2, L=[], R=[] | M0([1], [1]) | 11 | `macro_sweep_solo_to_zero` ✓ |
| c = 1, L=(a+1)::L' | M(L', a+1, 1::d::R) | 6 | `macro_shift` ✓ |

### From M0_Config (a::L) R:

| Condition | Result | Steps | Theorem |
|-----------|--------|-------|---------|
| R = [1] | M(L, a+6, []) | 8 | `macro_era_complete` ✓ |
| R = [2] | M(L, a+3, [1]) | 8 | `macro_zero_two_solo` ✓ (just proven) |
| R = [3] | M0((a+4)::L, [1]) | 12 | `macro_zero_bounce_to_zero` ✓ |
| R = [z+4] | M((a+4)::L, z+1, [1]) | z+13 | `macro_zero_bounce` ✓ |
| R = 2::d::R' | M(L, a+3, (d+1)::R') | 8 | `macro_zero_two` ✓ |
| R = 1::(z+1)::R' | **HALT** | 6 | `macro_halt` ✓ |
| R = r₁::...::rₙ, r₁≥4, n≥2, rₙ≥2 | M(rev(r₂..rₙ₋₁)++[r₁-2,a+4]++L, rₙ-1, [1]) | varies | **NOT YET PROVEN** |
| R = r₁::...::rₙ, r₁≥4, n≥2, rₙ=1 | M0(rev(r₂..rₙ₋₁)++[r₁-2,a+4]++L, [1]) | varies | **NOT YET PROVEN** |

### Remaining gaps in M_Config rules:

52 gap events found in 200K steps:
- M([], c, d::R) where R nonempty — L=[] with R≠[] (not solo)
- M(L, c, []) where L nonempty — R=[] with L≠[] (not solo)

These come from:
- M(L, c, []) arises from `macro_era_complete` → M(L', a+6, []) when L' nonempty
- M([], c, R) arises from multi-run bounce producing M([], ..., [1])

## Multi-run zero bounce pattern (VERIFIED, 0 mismatches over 200K steps)

For M0_Config (a::L) (r₁ :: r₂ :: ... :: rₙ) where r₁ ≥ 4:

**Output L** = [rₙ₋₁, rₙ₋₂, ..., r₂, r₁-2, a+4] ++ L  (reversed interior runs, then r₁-2, then a+4, then original L)

**Output cursor** = rₙ - 1

**Output R** = [1]

If rₙ = 1: output is M0_Config instead of M_Config (cursor = 0).

### Verified examples:
```
M0([13], [8, 3]) → M([6, 17], (2), [1])     -- r1-2=6, a+4=17, r2-1=2 ✓
M0([49], [30, 7]) → M([28, 53], (6), [1])    -- r1-2=28, a+4=53, r2-1=6 ✓
M0([2], [6, 6, 2]) → M([6, 4, 6], (1), [1]) -- r2=6, r1-2=4, a+4=6, r3-1=1 ✓
M0([3], [4, 7, 14, 2]) → M([14, 7, 2, 7], (1), [1]) -- r3=14, r2=7, r1-2=2, a+4=7, r4-1=1 ✓
M0([115], [40, 1]) → M0([38, 119], [1])      -- r1-2=38, a+4=119, r2=1 → M0 ✓
```

### Step count for multi-run bounce:
5 (initial BCD) + (r₁-3) F_shift + sum over interior zeros (3 bounce + rᵢ F_shift) + final edge sequence

Composition of existing lemmas: a0_to_b, B,0→C, C,0→D, d1_to_b, b1_to_f, F_shift, f_bounce_interior (repeated), bcd_extension.

## Key insight for halting

**HALT fires only when M0_Config has R = 1::(z+1)::R' with z+1 ≥ 1.**

But every non-halt M0 rule produces R = [1] (a single element). And M0(L, [1]) triggers era_complete → M(L', a+6, []).

The ONLY way to get M0 with |R| > 1 is via `macro_sweep_to_zero`, which produces M0(L', (d+1)::R'). For this to match the HALT pattern, we'd need d+1 = 1 (so d=0) and |R'| ≥ 1 with R'[0] ≥ 1.

**d=0 means a zero-valued run** (two consecutive zero-markers). Simulation over 500K steps confirms: **zero-valued runs never appear in any M_Config or M0_Config R or L list.** All runs are ≥ 1.

So the non-halting proof at the macro level reduces to:
**Prove that all runs in reachable macro configurations are ≥ 1.**

This is a DIFFERENT (and potentially simpler) formulation of c1_never_reached!

## Remaining gaps to fill for complete macro_step

1. **Multi-run zero bounce** (44 events in 200K steps): Prove by induction on |R|, composing F_shift + f_bounce_interior
2. **R=[2] terminal** (9 events): DONE — `macro_zero_two_solo` just proven
3. **Sweep with L=[] R≠[]** and **L≠[] R=[]**: Need new theorems for one-sided sweeps
4. **R = 3::d::R'** (r₁=3 with multiple runs): Subcase of multi-run, needs r₁=3 variant
5. **M_Config with c=1, L=[0,...] or L=[]**: Need to check if reachable (probably not if all runs ≥ 1)
