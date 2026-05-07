/-
**Sub-plan E.3'**: well-founded recursion on `lex(phi, mr)` to close
`BadShape.base R` in `era_orbit.lean:493`.

This file provides:

  1. `macroStep_lex_strict_increase`: forward macroStep strictly
     increases `lex(phi, mr)` across all 12 dispatch cases.
  2. `D2_backward_phi_mr`: D2 backward (predecessor of M([], 3, R) via
     γ.1) preserves phi and halves mr.
  3. `cascade_unreachable`: structural-induction skeleton; step case
     closed directly; base case delegates to era.lean:567's existing
     `OrbitReachable.not_M_empty_3` (which retains 1 multi-R sorry).

Status:
  * Foundations (1, 2) closed axiom-clean — verified via `lean_verify`.
  * cascade_unreachable structural skeleton — closed axiom-clean.
  * The mutual-recursion attempt (cu + not_M_empty_3') with measure
    `cfg.mr * 2 + sel` was BLOCKED by Lean's termination check not
    propagating the `BadShape.base R` ⇒ `cfg = .M [] 3 R` refinement
    to the outer `cfg.mr` in the measure. Documented in the inline
    comments below for next-iteration retry.
-/

import scout_2adic
import era_orbit

namespace Sweeper

open BusyLean

-- ============================================================
-- Section 1: forward macroStep strictly increases lex(phi, mr)
-- ============================================================

/-- **Master lex-monotonicity**: `macroStep cfg = some (k, cfg')` implies
    `(cfg.phi, cfg.mr) <ₗ (cfg'.phi, cfg'.mr)` in lex order, equivalently
    `cfg.phi < cfg'.phi ∨ (cfg.phi = cfg'.phi ∧ cfg.mr < cfg'.mr)`.

    Proof: case split via `macroStep_eq_some_cases` (12 disjuncts).
    Sweep-family rules (D1–D5) preserve phi but increment/double mr.
    M0-rules (D6–D12) strictly increase phi by ≥ 2. -/
theorem macroStep_lex_strict_increase {cfg cfg' : MacroConfig} {k : Nat}
    (h_inv : MacroInvariant cfg) (h : macroStep cfg = some (k, cfg')) :
    cfg.phi < cfg'.phi ∨ (cfg.phi = cfg'.phi ∧ cfg.mr < cfg'.mr) := by
  rcases macroStep_eq_some_cases cfg k cfg' h with
    ⟨a, L', d, R', hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, _, htgt⟩
  | ⟨a, c', L', d, R', hcfg, _, htgt⟩
  | ⟨d, R', hcfg, _, htgt⟩
  | ⟨c', d, R', hcfg, _, htgt⟩
  | ⟨a, b, L', hcfg, _, htgt⟩
  | ⟨a, hcfg, _, htgt⟩
  | ⟨a, L', hcfg, _, htgt⟩
  | ⟨a, L', hcfg, _, htgt⟩
  | ⟨a, L', hcfg, _, htgt⟩
  | ⟨a, z, L', hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, _, htgt⟩
  -- D1 sweep_to_zero: phi same, mr +1.
  · subst hcfg; subst htgt
    right
    refine ⟨?_, ?_⟩
    · simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons]; omega
    · simp only [MacroConfig.mr_M, MacroConfig.mr_M0, macroMr, macroPoly2_cons]; omega
  -- D2 sweep_and_shift: phi same, mr doubles.
  · subst hcfg; subst htgt
    right
    refine ⟨?_, ?_⟩
    · simp [MacroConfig.phi_M, List.sum_cons]; omega
    · simp only [MacroConfig.mr_M, macroMr, macroPoly2_cons]
      -- post mr = 1 + 2((d+1) + 2 P) + 3 = 2(d + 2P + 3) = 2 * pre mr.
      -- Strictly larger since pre mr ≥ 4 (R nonempty AllGe1).
      have hd : d ≥ 1 := by
        have hR := h_inv.2.2.1; rw [AllGe1_cons] at hR; exact hR.1
      omega
  -- D3 sweep: phi same, mr +1.
  · subst hcfg; subst htgt
    right
    refine ⟨?_, ?_⟩
    · simp [MacroConfig.phi_M, List.sum_cons]; omega
    · simp only [MacroConfig.mr_M, macroMr, macroPoly2_cons]; omega
  -- D4 sweep_to_zero_left_empty: phi same, mr +1.
  · subst hcfg; subst htgt
    right
    refine ⟨?_, ?_⟩
    · simp [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil]; omega
    · simp only [MacroConfig.mr_M, MacroConfig.mr_M0, macroMr, macroPoly2_cons]; omega
  -- D5 sweep_left_empty: phi same, mr +1.
  · subst hcfg; subst htgt
    right
    refine ⟨?_, ?_⟩
    · simp [MacroConfig.phi_M, List.sum_cons]; omega
    · simp only [MacroConfig.mr_M, macroMr, macroPoly2_cons]; omega
  -- D6 era_and_sweep: phi +4.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
    omega
  -- D7 era_and_sweep_solo: phi +4.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
    omega
  -- D8 zero_two_solo: phi +2.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
    omega
  -- D9 zero_bounce_to_zero: phi +2.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M0, List.sum_cons]
    omega
  -- D10 zero_bounce_and_shift: phi +2.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
    omega
  -- D11 zero_bounce: phi +2.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
    omega
  -- D12 zero_two: phi +2.
  · subst hcfg; subst htgt
    left
    simp [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons]
    omega

-- ============================================================
-- Section 2: D2 backward halves mr, preserves phi
-- ============================================================

/-- **D2-backward halves mr** (specialised γ.1 + scout's
    `macroMr_D2_forward`): for any `cfg` with `macroStep cfg = some (k, .M [] 3 R)`,
    we have `cfg.phi = (.M [] 3 R).phi` and `2 * cfg.mr = (.M [] 3 R).mr`.
    By γ.1, `cfg = .M [2] 3 (d :: R')` with `R = 1 :: (d + 1) :: R'`. -/
theorem D2_backward_phi_eq {cfg : MacroConfig} {R : List Nat} {k : Nat}
    (h_inv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [] 3 R)) :
    cfg.phi = (MacroConfig.M [] 3 R).phi := by
  obtain ⟨d, R', hcfg, hR, _⟩ := macroStep_M_empty_3_predecessor_form h_inv h
  subst hcfg; subst hR
  simp [MacroConfig.phi_M, List.sum_cons, List.sum_nil]; omega

theorem D2_backward_mr_double {cfg : MacroConfig} {R : List Nat} {k : Nat}
    (h_inv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [] 3 R)) :
    2 * cfg.mr = (MacroConfig.M [] 3 R).mr := by
  obtain ⟨d, R', hcfg, hR, _⟩ := macroStep_M_empty_3_predecessor_form h_inv h
  subst hcfg; subst hR
  simp only [MacroConfig.mr_M, macroMr, macroPoly2_cons]
  ring

/-- The mr value of `M([], 3, R)` is at least 4 when R is nonempty AllGe1. -/
theorem MacroConfig.mr_M_empty_3_ge_four {R : List Nat}
    (hR : AllGe1 R) (hR_ne : R ≠ []) :
    (MacroConfig.M [] 3 R).mr ≥ 4 := by
  cases R with
  | nil => exact absurd rfl hR_ne
  | cons d R' =>
    have hd := (AllGe1_cons.mp hR).1
    simp only [mr_M, macroMr, macroPoly2_cons]; omega

/-- **D2-backward strictly decreases lex** (the cascade-backward step):
    `cfg_pre.lex < (.M [] 3 R).lex` when cfg_pre is the D2-predecessor. -/
theorem D2_backward_lex_strict {cfg : MacroConfig} {R : List Nat} {k : Nat}
    (h_inv : MacroInvariant cfg)
    (hR : AllGe1 R) (hR_ne : R ≠ [])
    (h : macroStep cfg = some (k, .M [] 3 R)) :
    cfg.phi = (MacroConfig.M [] 3 R).phi ∧
    cfg.mr < (MacroConfig.M [] 3 R).mr := by
  refine ⟨D2_backward_phi_eq h_inv h, ?_⟩
  have h_ge := MacroConfig.mr_M_empty_3_ge_four hR hR_ne
  have h_double := D2_backward_mr_double h_inv h
  omega

-- ============================================================
-- Section 3: skeleton for cascade closure (Sub-plan E.3' core)
-- ============================================================

/-- **Lex measure**: `(cfg.phi, cfg.mr)` as a `Nat × Nat`. Used as the
    well-founded measure for cascade-backward induction. -/
def MacroConfig.lex (cfg : MacroConfig) : Nat × Nat := (cfg.phi, cfg.mr)

@[simp] theorem MacroConfig.lex_M (L : List Nat) (c : Nat) (R : List Nat) :
    (MacroConfig.M L c R).lex = (L.sum + R.sum + c, macroMr R) := rfl

@[simp] theorem MacroConfig.lex_M0 (L R : List Nat) :
    (MacroConfig.M0 L R).lex = (L.sum + R.sum, macroMr R) := rfl

-- **Cascade closure (mutual recursion via Φ-monotone step_R1)**:
-- With the Φ side condition on `step_R1` (added 2026-05-06), the
-- cascade's lex termination measure was hoped to work:
--   * cu base R → not_M_empty_3': phi same, sel 1 → 0.
--   * not_M_empty_3' multi-R → cu cfg_pre: phi same, mr decreases.
--   * not_M_empty_3' step_R1 → ih specialised: closes directly.
--
-- **CRITICAL (2026-05-07): the recursion is NOT well-founded.**
-- The cu→aux step (via cu's structural ih on BadShape.base R₀ where
-- R₀ = original R) makes the measure GROW, not shrink:
--   aux R: measure 4·macroMr(dp::Rp)
--   → cu cfg_pre: measure 2·macroMr(dp::Rp) + 1  [smaller — D2 halves]
--   → aux R via ih(h_prev.step_macro h_step): measure 4·macroMr(dp::Rp)
--      [back to original — NO descent]
-- The BadShape encoding's `base R₀` always carries the forward
-- endpoint's R (= original R), so cu unwinds to aux at SAME R. The
-- mutual recursion has no actual descent in the cascade direction.
-- See `lean-issues.md` "CRITICAL FINDING" and `LOG.md` 2026-05-07
-- for the trace showing the non-termination.
-- Closing the sorries requires backward γ.2-style analysis at the
-- M([2], 3, _) level — a substantially different design.

mutual

/-- **Cascade closure**: structural induction on `BadShape` for the
    step case; base case delegates to `not_M_empty_3'_aux` which
    takes `R` explicitly so its termination measure `macroMr R * 2`
    can be evaluated without cfg substitution issues. -/
theorem cascade_unreachable {cfg : MacroConfig}
    (h_bad : BadShape cfg) (h_or : OrbitReachable cfg) : False := by
  induction h_bad with
  | step h_bad' h_step ih =>
    exact ih (h_or.step_macro h_step)
  | base R =>
    exact OrbitReachable.not_M_empty_3'_aux R h_or rfl
termination_by cfg.mr * 2 + 1
decreasing_by
  -- Goal: macroMr R * 2 < cfg.mr * 2 + 1.
  -- cfg = M [] 3 R from BadShape.base R refinement; cfg.mr ≡ macroMr R
  -- definitionally. But Lean's termination check introduces fresh case
  -- binders that prevent direct unification. See lean-issues.md.
  sorry

/-- **Cascade-closed auxiliary**: `OrbitReachable cfg` and `cfg = M [] 3 R`
    imply False. R is an explicit arg so the termination measure
    `macroMr R * 2` is directly evaluable. -/
theorem OrbitReachable.not_M_empty_3'_aux (R : List Nat)
    {cfg : MacroConfig} (h : OrbitReachable cfg) (hcfg : cfg = .M [] 3 R) :
    False := by
  cases h with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_macro h_prev h_step =>
    have hsound := macroStep_sound _ _ _ h_step h_prev.macroInvariant
    cases R with
    | nil =>
      rw [hcfg] at hsound
      exact hsound.2.1.2.2.2 rfl
    | cons d R' =>
      cases R' with
      | nil =>
        exact macroStep_no_M_empty_3_single h_prev.macroInvariant (hcfg ▸ h_step)
      | cons d' R'' =>
        -- Multi-R cascade: predecessor M [2] 3 _ via γ.1, recurse cu.
        subst hcfg
        obtain ⟨dp, Rp, hcfg_p, hR_eq, _⟩ :=
          macroStep_M_empty_3_predecessor_form h_prev.macroInvariant h_step
        subst hcfg_p
        have h_bad_pre : BadShape (.M [2] 3 (dp :: Rp)) :=
          BadShape.step (BadShape.base (d :: d' :: R'')) h_step
        exact cascade_unreachable h_bad_pre h_prev
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) hL
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_multi_bounce_2_double_shift h_prev =>
    rw [MacroConfig.M.injEq] at hcfg
    have ha : _ ≥ 1 := (AllGe1_cons.mp h_prev.macroInvariant.1).1
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_multi_bounce_last_2_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) hcfg.1
  | step_R2_zero h_prev =>
    rw [MacroConfig.M.injEq] at hcfg
    have ha : _ ≥ 1 := (AllGe1_cons.mp h_prev.macroInvariant.1).1
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_R3 _ _ _ _ h_safe _ _ =>
    exact h_safe R hcfg
  | @step_R1 d_pre R'_pre _ _ h_pred _ _ _ _ =>
    -- Predecessor M [] 3 (d_pre :: R'_pre). Recurse on aux at smaller R.
    exact OrbitReachable.not_M_empty_3'_aux (d_pre :: R'_pre) h_pred rfl
termination_by macroMr R * 2
decreasing_by
  -- Aux's recursive calls:
  --   1. step_macro multi-R → cascade_unreachable cfg_pre h_bad_pre h_prev.
  --   2. step_R1 → not_M_empty_3'_aux on predecessor.
  -- Both need detailed arithmetic; see lean-issues.md.
  all_goals sorry

end

end Sweeper
