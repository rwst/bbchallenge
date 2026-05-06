/-
**Scout: parity argument for `BadShape.base R` closure**.

Hypothesis to test: the backward `macroStep` chain from `M([], 3, R)`
keeps cursor in odd values {3, 5, 7, …}; init has cursor 4 (even); so
the pure M→M chain cannot terminate at init.

Findings (see comments at each stage):

  1. **M→M predecessor of M([], 3, R) has cursor=3** (γ.1 gives it as
     `M([2], 3, d::R')` directly). ✓ Odd.

  2. **M→M predecessor of M(L, 3, R) with L = 2-spine** has cursor ∈
     {3, 5} (γ.2). ✓ Both odd.

  3. **D3 backward in general** lifts cursor from c → c+2; D5 backward
     similarly. So ALL M→M backward steps in the cursor=3 cascade
     produce odd cursors. ✓

  4. **M0→M backward** is the parity-breaker. But the cursor=3 cascade
     has only ONE M0→M producer (D11), and D11 requires output L head
     ≥ 5, which fails for `M([], 3, R)`. So the immediate cascade from
     M([], 3, R) is purely M→M. ✓

  5. **Where parity stops being enough**: when the M-segment grows L
     via D2-spine, then a later layer can reach `M((a+4) :: L', 3, [1])`
     (a ≥ 1) which IS a valid D11 backward target. So the cascade can
     branch into M0 land at SOME cursor=3 layer.

Conclusion: parity (cursor stays odd along M→M cascade from M([], 3, R))
is provable as a structural fact, but it is NOT a standalone closure.
It must be combined with M↔M0 transition counting (Φ-bounded by
≤ `(Φ-6)/2` jumps) to get a finite total cascade depth.

Standalone parity rating after scout: insufficient.
Combined with Φ-segment-counting: viable but essentially equivalent
work to Path 2 (era-graded D2-spine bound).

This file is **scouting only**: not part of the main library build
(roots in `lakefile.toml` exclude it). To build: add to roots, then
`lake build Sweeper`. The proofs verify the parity claim is real but
also expose the gap.
-/

import era_orbit_gamma

namespace Sweeper

open BusyLean

-- ============================================================
-- Probe 1: M-side predecessor of M([], 3, R) has cursor = 3
-- ============================================================

/-- **Parity probe (level 0)**: any `macroStep` predecessor of
    `M([], 3, R)` is itself an M-config with cursor = 3 (specifically
    `M([2], 3, d :: R')`). Direct corollary of γ.1.

    This rules out M0 predecessors (none can produce M([], 3, R)) and
    fixes the predecessor cursor as 3 (odd). -/
theorem scout_parity_M_empty_3
    {cfg : MacroConfig} {R : List Nat} {k : Nat}
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [] 3 R)) :
    ∃ d R', cfg = .M [2] 3 (d :: R') := by
  obtain ⟨d, R', hcfg, _, _⟩ := macroStep_M_empty_3_predecessor_form hinv h
  exact ⟨d, R', hcfg⟩

-- ============================================================
-- Probe 2: M-side predecessor of M(2::L_out, 3, R) has cursor ∈ {3, 5}
-- ============================================================

/-- **Parity probe (level 1)**: the predecessor of `M(2 :: L_out, 3, R)`
    has cursor in {3, 5}, both odd. Direct corollary of γ.2. -/
theorem scout_parity_M_2list_3_clean
    {cfg : MacroConfig} {L_out : List Nat} {R : List Nat} {k : Nat}
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (2 :: L_out) 3 R)) :
    ∃ L c R_pre, cfg = .M L c R_pre ∧ (c = 3 ∨ c = 5) := by
  rcases macroStep_M_2list_3_predecessor_form hinv h with
    ⟨d, R', hcfg, _, _⟩ | ⟨d, R', hcfg, _, _⟩
  · exact ⟨_, 3, _, hcfg, Or.inl rfl⟩
  · exact ⟨_, 5, _, hcfg, Or.inr rfl⟩

-- ============================================================
-- Probe 3: explicit init mismatch (cursor parity)
-- ============================================================

/-- **Parity probe (init mismatch)**: init has cursor 4; cursor-3 configs
    are not init. Trivial structural fact, but the keystone of the
    parity argument: if M→M chain keeps cursor odd and eventually must
    reach init, contradiction. -/
theorem scout_init_cursor_even :
    ∀ R, (.M [1] 4 [1] : MacroConfig) ≠ .M [] 3 R := by
  intro R hcfg
  injection hcfg with hL _ _
  exact List.cons_ne_nil 1 [] hL

-- ============================================================
-- Probe 4: gap demonstration — M0 predecessors at cursor=3
-- ============================================================

/-- **Gap demonstration**: at cursor=3 with L head ≥ 5, the M0→M
    transition D11 (`zero_bounce`) IS a valid predecessor. This breaks
    the pure-parity argument: a cursor=3 M-config can have an M0
    predecessor with no cursor.

    Specifically, `M((a+4) :: L', 3, [1])` has predecessor `M0(a :: L', [6])`
    (D11 with z=1). For example: `M([5], 3, [1])` ← `M0([1], [6])`.

    This means the parity argument needs M↔M0 transition counting
    (Path 2's territory). Pure parity is insufficient. -/
theorem scout_M0_predecessor_at_cursor_3 (a : Nat) (L' : List Nat) :
    macroStep (.M0 (a :: L') [6]) = some (15, .M ((a + 4) :: L') 3 [1]) := by
  -- D11: z = 1, z+5 = 6, z+2 = 3, k = z + 1 + 13 = 15.
  rfl

/-- **Gap demonstration (continued)**: this M0 predecessor IS reachable
    when its Φ ≥ 6 — e.g., `M0([2], [6])` has Φ = 8 ≥ 6, so Φ-pruning
    doesn't exclude it. Hence the parity argument cannot close the
    M([5], 3, [1]) cascade subcase. -/
example : MacroConfig.phi (.M0 [2] [6]) = 8 := by
  simp [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]

end Sweeper
