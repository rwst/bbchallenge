# Gap Rules Discovery and Status (2026-04-04)

## Key Discovery: Unified Sweep Rules

ALL sweep rules (L empty, R empty, both, or neither) follow the SAME pattern:

```
M(L, c, R) → M(incr(L), c-2, incr(R))   for c ≥ 3, step count = 2c+7
M(L, 2, R) → M0(incr(L), incr(R))        for c = 2, step count = 11

where incr(a::rest) = (a+1)::rest, incr([]) = [1]
```

This was verified by Python simulation over 125 test cases (all L/R combinations, c=3..20).

## Theorems Added to machine.lean (4 gap rules)

### 1. macro_sweep_left_empty (line ~741) — NEEDS FIX
Statement: `M_Config [] (c+3) (d::R) → M_Config [1] (c+1) ((d+1)::R)` in 2*(c+3)+7 steps.
Proof: phased rw approach (same as macro_sweep_solo), following A_shift → a0_to_b → b1_to_f → F_shift → f_bounce_interior → f0_d0_to_e → E,1→A.
**Error**: "unsolved goals" at the final match step.
**Fix needed**: The `conv_rhs => rw [M_Config_cons, ..., runs_succ]` then `simp only [runs_singleton, ones_succ, ones_zero, List.nil_append]` — may need adjustment. The issue is that `runs [1]` needs to be reduced to `[true]`, requiring `runs_singleton` + `ones_succ` + `ones_zero`.

### 2. macro_sweep_to_zero_left_empty (line ~774) — NEEDS FIX
Statement: `M_Config [] 2 (d::R) → M0_Config [1] ((d+1)::R)` in 11 steps.
Proof: simp-only approach (like macro_sweep_to_zero).
**Error**: "unsolved goals" — simp finishes but doesn't close.
**Fix needed**: Removed sw_D0, sw_D1, sw_E1 (unused warnings). May need M_Config_nil + M0_Config_cons instead of M_Config + M0_Config. Or add listHead_nil, listTail_nil. The L=[] case unfolds differently through M_Config.

### 3. macro_sweep_right_empty (line ~783) — NEEDS TESTING
Statement: `M_Config (a::L) (c+3) [] → M_Config ((a+1)::L) (c+1) [1]` in 2*(c+3)+7 steps.
Proof: phased rw approach (same as macro_sweep).
**Potential issue**: Same as #1 — `runs_singleton` at the end may leave `ones 1` unreduced. The `conv_rhs` uses `runs_succ, runs_singleton` — may also need `ones_succ, ones_zero`.

### 4. macro_sweep_to_zero_right_empty (line ~814) — NEEDS TESTING
Statement: `M_Config (a::L) 2 [] → M0_Config ((a+1)::L) [1]` in 11 steps.
Proof: simp-only approach.
**Potential issue**: Needs `runs_nil` for R=[] side. May need adjustments like #2.

## Proof Strategy for Fixing

### For phased rw proofs (#1, #3):
The final match step needs to reduce `runs [1]` fully. Options:
1. Replace `conv_rhs => rw [...]` with `simp only [M_Config_cons, runs_succ, runs_singleton, ones_succ, ones_zero, show c+1-1=c from by omega]`
2. Add `ones_succ, ones_zero` after runs_singleton in the rw chain
3. Use `norm_num` or `rfl` after the conv_rhs to close remaining goal

The working macro_sweep_solo proof (line 730) uses:
```
simp only [M_Config_cons, show c + 1 - 1 = c from by omega, runs_singleton, ones_succ, ones_zero]
```
This is a simp (not conv_rhs rw), and it includes ones_succ + ones_zero. **Follow this pattern.**

### For simp proofs (#2, #4):
The issue is that M_Config [] 2 R unfolds via M_Config_nil (left = ones(1) = [true]) while the original macro_sweep_to_zero uses M_Config (the raw def) which does case matching. Options:
1. Use `M_Config_nil, M0_Config_cons` instead of `M_Config, M0_Config` in the simp set
2. Add `listHead_nil, listTail_nil` for the L=[] path
3. Add `runs_nil` for R=[] output side

## Remaining Work After Gap Rules

1. **Multi-run zero bounce** (M0 with R = r₁::...::rₙ, r₁≥4, n≥2) — NOT PROVEN, 44/97 M0 events
2. **R=3::d::R'** (r₁=3 with multiple runs) — subcase of multi-run bounce
3. **Define macro_step function** in Lean (big match on config type)
4. **Prove "all runs ≥ 1" invariant** — the core of the non-halting proof
5. **Derive sweeper_never_halts** from invariant

## Key Mathematical Result (VERIFIED)

The "all runs ≥ 1" invariant is:
- TRUE: Verified over 500K steps, zero violations
- TRIVIALLY PRESERVED: Every macro rule output has runs ≥ 1 when inputs ≥ 1:
  - incr produces a+1 ≥ 1 or [1]
  - macro_shift: cursor a+1 ≥ 1, new run = 1
  - era_complete: cursor a+6 ≥ 7
  - zero_bounce: cursor z+1 ≥ 1, new run = 1, left a+4 ≥ 4
  - zero_two: cursor a+3 ≥ 3, run d+1 ≥ 1
  - multi-run bounce: left a+4, run r-2 ≥ 2 (r≥4), cursor rₙ-1 ≥ 1 (rₙ≥2)
- PREVENTS HALT: HALT needs M0 R = 1::(z+1)::R'. But M0 with |R|>1 only comes from sweep_to_zero producing (d+1)::R'. If d ≥ 1 (invariant), then d+1 ≥ 2 ≠ 1. HALT can't fire.
- INITIAL: M_Config [] 6 [] has no runs at all (vacuously true)
