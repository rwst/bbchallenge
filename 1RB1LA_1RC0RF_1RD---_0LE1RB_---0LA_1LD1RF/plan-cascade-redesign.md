# Cascade redesign (2026-05-07)

Replaces the failed Sub-plan E.3′ cu/aux mutual recursion (see
`lean-issues.md` "CRITICAL FINDING" — that recursion is mathematically
not well-founded).

## Core insight

The previous `BadShape`-based design recursed FORWARD (cfg → cfg' via
macroStep). Forward steps INCREASE (phi, mr) — the wrong direction.

**Right direction**: recurse BACKWARD on `OrbitReachable`'s
`step_macro` constructor. Backward steps DECREASE (phi, mr) — by
`macroStep_lex_strict_increase` (already proved, axiom-clean).

## Predicate

```lean
def Is2Spine : List Nat → Prop
  | [] => True
  | x :: xs => x = 2 ∧ Is2Spine xs

inductive InCascade : MacroConfig → Prop where
  | mk_M_empty_3   (R : List Nat) : InCascade (.M [] 3 R)
  | mk_M_2spine_3  (L : List Nat) (R : List Nat)
                   (h_2s : Is2Spine L) (h_ne : L ≠ []) :
      InCascade (.M L 3 R)
  | mk_M_1_2spine_5 (L : List Nat) (R : List Nat)
                    (h_2s : Is2Spine L) :
      InCascade (.M (1 :: L) 5 R)
```

## Main theorem

```lean
theorem cascade_strong (cfg : MacroConfig)
    (h_in : InCascade cfg) (h_or : OrbitReachable cfg) : False
termination_by (cfg.phi, MacroConfig.lex.snd cfg)
```

Lex measure on `(phi, mr)`. Backward step strictly decreases by
`macroStep_lex_strict_increase`.

## Cases

For each `OrbitReachable` constructor:

* `init`: `cfg = M [1] 4 [1]`. Not in cascade (cursor 4, not 3 or 5; or
  L head 1 ≠ 2 for `mk_M_2spine_3`; cursor 4 ≠ 5 for `mk_M_1_2spine_5`).

* `step_macro h_prev h_step`: predecessor `cfg_pre` exists.
  - Need `InCascade cfg_pre` to recurse.
  - Cases on `h_in`:
    * `mk_M_empty_3 R`: γ.1 gives `cfg_pre = M [2] 3 (d :: R')`.
      InCascade via `mk_M_2spine_3 [2]`. ✓
    * `mk_M_2spine_3 L R`: γ.2 gives D2 ext (`M (2 :: L) 3 _`) or
      D3 lift (`M (1 :: L_tail) 5 _` if L = 2 :: L_tail).
      Both InCascade. ✓
    * `mk_M_1_2spine_5 L R`: **γ.3 needed**. Predecessor cases:
      D2 (M [4, 1, 2^n] 3 _) — NOT in InCascade.
      D5 (M [] 7 _) — NOT in InCascade.
      D7 (M0 [2] [1]) — NOT in InCascade.
      D8 (M0 [2, 1, 2^n] [2]) — NOT in InCascade.
      D12 (M0 [2, 1, 2^n] [2, d, ...]) — NOT in InCascade.

      **Problem**: `mk_M_1_2spine_5`'s predecessors leave the cascade.
      We'd need to extend InCascade or prove these predecessors
      contradict OrbitReachable.

* `step_R1 h_pred ... h_phi`: predecessor `M [] 3 (d :: R')` ∈ InCascade
  via `mk_M_empty_3`. `cfg.phi ≥ predecessor.phi + 2` ⇒ recurse with
  smaller phi. ✓ (assuming cfg ∈ InCascade so `cfg.phi` is in scope).

* Other constructors (`step_multi_bounce_*`, `step_R2_*`, `step_R3`):
  output shape doesn't match any InCascade form. Trivial via injection.

## Open issue: `mk_M_1_2spine_5` predecessors leave cascade

The predecessors of `M (1 :: L_2s) 5 R` are:

| Rule | Predecessor                                        | In cascade? |
|------|----------------------------------------------------|-------------|
| D2   | `M (4 :: 1 :: L_2s) 3 (d :: R')`                   | No (L head=4) |
| D5   | `M [] 7 (d :: R')`                                 | No (cursor=7) |
| D7   | `M0 [2] [1]`                                       | No (M0)     |
| D8   | `M0 (2 :: 1 :: L_2s) [2]`                          | No (M0)     |
| D12  | `M0 (2 :: 1 :: L_2s) (2 :: d :: R')`               | No (M0)     |

To close the cascade, **at least one** of these must hold for each:

A. The predecessor shape is excluded by some Φ / parity argument.
B. The predecessor's predecessors are themselves analysed (recursive
   extension of InCascade).

### Argument A candidates

* **D2 (M (4 :: 1 :: L_2s) 3 _)**: L head = 4. Φ analysis:
  predecessor.phi = 4 + 1 + L_2s.sum + (d::R').sum + 3 =
  L_2s.sum + d + R'.sum + 8. Original cfg.phi = 1 + L_2s.sum + R.sum +
  5. With R = 1 :: (d+1) :: R', cfg.R.sum = 1 + d + 1 + R'.sum =
  d + R'.sum + 2. So cfg.phi = L_2s.sum + d + R'.sum + 8 = same as
  predecessor.phi. **No Φ gap.**

  But `(4 :: 1 :: L_2s)` violates 2-spine constraint, so we'd need an
  era-graded argument that L can never have a 4 at head.

* **D5 (M [] 7 _)**: cursor 7. Φ analysis: predecessor.phi = (d::R').sum
  + 7 = d + R'.sum + 7. cfg.phi = 1 + L_2s.sum + R.sum + 5 = ... need
  to compute. R = (d+1) :: R'. cfg.phi = 1 + L_2s.sum + d + 1 + R'.sum
  + 5 = L_2s.sum + d + R'.sum + 7. So predecessor.phi - cfg.phi =
  -L_2s.sum. Since L_2s.sum = 2 * |L_2s|, this is ≤ 0. predecessor.phi
  ≤ cfg.phi (consistent with forward Φ-monotone). For L_2s = []
  (n=0): predecessor.phi = cfg.phi (no descent). For L_2s ≠ [] (n≥1):
  predecessor.phi < cfg.phi (descent in lex first coord). So when
  L_2s ≠ [], the recursion makes phi-progress. But for L_2s = [] case
  (cfg = M [1] 5 R), predecessor M [] 7 (d::R') has same phi.
  Then we'd need mr-descent or further analysis.

  Hmm: cfg.r_mr = macroMr R = macroMr ((d+1)::R') = (d+1) + 2*macroMr R'
  + 3. predecessor.r_mr = macroMr (d::R') = d + 2*macroMr R' + 3.
  cfg.r_mr - predecessor.r_mr = 1. So mr decreases by 1 backward.
  Combined with phi same (when L_2s = []), lex descent works.

* **D7 (M0 [2] [1])**: SPECIFIC config. We'd need to show `M0 [2] [1]
  ∉ OrbitReachable`. Empirically (era data), M0 [2] [1] doesn't occur,
  but proving this formally requires another chain.

* **D8/D12 (M0 (2 :: 1 :: L_2s) ...)**: M0 with specific L. Similar.

### Argument B (recursive extension)

Generalize InCascade to include these predecessor shapes, AND recurse
into their predecessors. Risk: unbounded expansion.

Bound the expansion via Φ ceiling: for OrbitReachable cfg in any
analysed shape, Φ ≤ Φ-of-cfg. So the cascade depth is bounded by Φ.

This works because Φ is non-decreasing forward (γ.3.3
`gammaFuel_macroStep_nondec`), so backward steps Φ is non-increasing.

If we use **lex (phi, mr)** as measure with phi as primary, the
recursion terminates when phi can't decrease further (i.e., reaches
init's phi = 6). At that point, OrbitReachable cfg with phi = 6
implies cfg ≅ init (specifically structure).

## Path forward (recommended)

1. **Define `InCascade` (broadened)**: include M0 shapes that arise as
   predecessors of `mk_M_1_2spine_5`. Specifically:
   - `mk_M0_2_1_2spine_2` (M0 (2 :: 1 :: L_2s) [2])
   - `mk_M0_2_1_2spine_2_R` (M0 (2 :: 1 :: L_2s) (2 :: d :: R'))
   - `mk_M0_2_1` (M0 [2] [1]) [might be subsumed by above with L_2s=[]]
   - `mk_M_4_1_2spine_3` (M (4 :: 1 :: L_2s) 3 R)
   - `mk_M_empty_7` (M [] 7 R)

2. **Prove γ.3, γ.4, γ.5, ...** for predecessor analysis at each shape.

3. **Verify lex termination**: lex(phi, mr) strictly decreases on every
   backward step.

4. **Cascade closure**: structural induction on InCascade + recursion
   on lex measure.

**Estimated effort**: 400–600 L new code (γ-analysis + cascade strong).

## Alternative: bound via Φ ceiling

Rather than per-shape analysis, use Φ as global descent:

```lean
theorem cascade_strong (cfg : MacroConfig)
    (h_in : InCascade cfg) (h_or : OrbitReachable cfg) : False := by
  -- Strong induction on cfg.phi (Nat).
  ...
```

Each step_macro recurse decreases phi by `macroStep_lex_strict_increase`
(when phi DOES decrease, which is most of the time). When phi same
(D-family rules preserve phi), use mr as secondary.

**Issue**: phi same on D-family means we need mr-induction within phi
levels. This is the lex measure again.

## Decision: scope

This redesign is substantially larger than a session's worth of work.
**Recommend**: stage incrementally:

* Stage 1 (this session): γ.3 + InCascade base/2spine_3 + cascade_strong
  for those two shapes only. Sorry-stub the `mk_M_1_2spine_5` case.
  Probably +200 L, retains 1 sorry.

* Stage 2 (future): γ.4 + extended InCascade for `mk_M_1_2spine_5`'s
  predecessors. +200 L.

* Stage 3 (future): close all sorries. +100 L.

## Risks

* The cascade may not actually terminate without empirical input
  (e.g., F2 conjecture). The era-sim data suggests no orbit visits
  M [] 3 _, but a formal proof of this might be very hard.
* The Φ-ceiling approach assumes phi-monotonicity for cascade closure,
  which is true forward (proved) but the BACKWARD lex descent needs
  careful tracking of when phi vs mr decreases.
