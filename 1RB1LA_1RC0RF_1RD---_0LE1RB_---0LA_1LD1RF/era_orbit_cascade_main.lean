/-
**Cascade main theorem** — `cascade_strong_aux` and `cascade_strong`,
extracted from `era_orbit_cascade.lean` for organization.

Imports `era_orbit_cascade_chains` which provides the chain helpers
used by `mk_M_empty_7` sub-cases.

3 sorries remain in `cascade_strong_aux`:
- mk_M_1_2spine_5 step_macro D2/D12 (CASE A original chain inflation)
- mk_M_empty_7 step_macro D12 (pred M0 [4] (2 :: d :: R'))
- mk_M_empty_7 multi_bounce_2_double_shift (pred M0 [c] [3, 2])
- mk_M_empty_7 R2_zero (pred M0 [c] [3, 1, 2])
- mk_M_empty_7 step_R3 (pred M0 [c] (...))

(plus 3 internal sorries inside `not_M_6_3_dR_via_ih` for D2/D3/step_R3.)
-/

import era_orbit_cascade_chains
import era_orbit_cascade_d2

namespace Sweeper

open BusyLean

-- ============================================================
-- Section 6: cascade_strong main theorem (Stage 1 skeleton)
-- ============================================================

/-- **Cascade closure auxiliary** (replaces failed Sub-plan E.3′ design):
    `InCascade cfg ∧ OrbitReachable cfg → False`. Proved by nested
    Nat strong induction on `(cfg.phi, cfg.mr)`. Outer ih covers
    smaller phi (any mr). Inner ih covers smaller mr at same phi.
    Backward `step_macro` decreases (phi, mr) lex by
    `macroStep_lex_strict_increase`. Forward step_R1 cases use the Φ
    side condition for phi-decrease.

    **Stage 1 status**: skeleton in place. Recursive calls handled
    via ih_phi / ih_mr. mk_M_1_2spine_5 case sorry-stubbed (Stage 2). -/
theorem cascade_strong_aux : ∀ phi : Nat, ∀ mr : Nat,
    ∀ cfg : MacroConfig, cfg.phi = phi → cfg.mr = mr →
      InCascade cfg → OrbitReachable cfg → False := by
  intro phi
  induction phi using Nat.strong_induction_on with
  | _ phi ih_phi =>
    intro mr
    induction mr using Nat.strong_induction_on with
    | _ mr ih_mr =>
      intro cfg h_phi h_mr h_in h_or
      subst h_phi
      subst h_mr
      cases h_or with
      | init => exact h_in.not_init
      | step_macro h_prev h_step =>
        -- Lex decrease via macroStep_lex_strict_increase.
        -- h_step : macroStep cfg_pre = some (k, cfg).
        -- macroStep_lex_strict_increase gives:
        --   cfg_pre.phi < cfg.phi ∨ (cfg_pre.phi = cfg.phi ∧ cfg_pre.mr < cfg.mr)
        have h_lex := macroStep_lex_strict_increase h_prev.macroInvariant h_step
        cases h_in with
        | mk_M_empty_3 R =>
          have h_in_pre := InCascade.step_macro_pre_M_empty_3
            h_prev.macroInvariant h_step
          rename_i cfg_pre _
          rcases h_lex with h_phi_lt | ⟨h_phi_eq, h_mr_lt⟩
          · exact ih_phi cfg_pre.phi h_phi_lt cfg_pre.mr cfg_pre rfl rfl h_in_pre h_prev
          · exact ih_mr cfg_pre.mr h_mr_lt cfg_pre h_phi_eq rfl h_in_pre h_prev
        | @mk_M_2spine_3 L R h_2s h_ne =>
          cases L with
          | nil => exact h_ne rfl
          | cons l_head L_tail =>
            obtain ⟨h_head, h_tail⟩ := h_2s
            subst h_head
            have h_in_pre := InCascade.step_macro_pre_M_2spine_3 (L_out := L_tail)
              h_tail h_prev.macroInvariant h_step
            rename_i cfg_pre _
            rcases h_lex with h_phi_lt | ⟨h_phi_eq, h_mr_lt⟩
            · exact ih_phi cfg_pre.phi h_phi_lt cfg_pre.mr cfg_pre rfl rfl h_in_pre h_prev
            · exact ih_mr cfg_pre.mr h_mr_lt cfg_pre h_phi_eq rfl h_in_pre h_prev
        | @mk_M_1_2spine_5 L_2s R h_2s =>
          -- cfg = M (1 :: L_2s) 5 R. macroStep cfg_pre = some (k, cfg).
          -- γ.3 enumeration: 4 productive cases (A, B, C, D).
          rename_i cfg_pre k
          rcases macroStep_eq_some_cases _ _ _ h_step with
            ⟨a, L', d, R', hcfg, _, htgt⟩  -- D1
          | ⟨a, L', d, R', hcfg, _, htgt⟩  -- D2 sweep_and_shift
          | ⟨a, c', L', d, R', hcfg, _, htgt⟩  -- D3 sweep
          | ⟨d, R', hcfg, _, htgt⟩  -- D4 sweep_to_zero_left_empty
          | ⟨c', d, R', hcfg, _, htgt⟩  -- D5 sweep_left_empty (CASE A)
          | ⟨a, b, L', hcfg, _, htgt⟩  -- D6 era_and_sweep
          | ⟨a, hcfg, _, htgt⟩  -- D7 era_and_sweep_solo (CASE B)
          | ⟨a, L', hcfg, _, htgt⟩  -- D8 zero_two_solo (CASE C)
          | ⟨a, L', hcfg, _, htgt⟩  -- D9 zero_bounce_to_zero
          | ⟨a, L', hcfg, _, htgt⟩  -- D10 zero_bounce_and_shift
          | ⟨a, z, L', hcfg, _, htgt⟩  -- D11 zero_bounce
          | ⟨a, L', d, R', hcfg, _, htgt⟩  -- D12 zero_two (CASE D)
          · -- D1: target M0, cfg is M. ⊥.
            exact MacroConfig.noConfusion htgt
          · -- D2 sweep_and_shift: target M L' (a + 1) (1 :: (d + 1) :: R').
            -- For target = M (1 :: L_2s) 5 R: L' = 1 :: L_2s, a + 1 = 5 → a = 4.
            -- Predecessor cfg_pre = M (4 :: 1 :: L_2s) 3 (d :: R'). L head 4 > 2.
            -- Hmm but L head 4 isn't in cascade. However, from MacroInvariant
            -- of cfg_pre, AllGe1 a ≥ 1 ✓. The shape isn't immediately excluded.
            -- For now: stub.
            sorry
          · -- D3 sweep: target M ((a + 1) :: L') (c' + 2) ((d + 1) :: R').
            -- For target M (1 :: L_2s) 5 R: a + 1 = 1 → a = 0. AllGe1 ⊥.
            injection htgt with hL hc hR
            injection hL with hh _
            subst hcfg
            have ha := (AllGe1_cons.mp h_prev.macroInvariant.1).1
            omega
          · -- D4 sweep_to_zero_left_empty: target M0. ⊥.
            exact MacroConfig.noConfusion htgt
          · -- D5 sweep_left_empty (CASE A): target M [1] (c' + 2) ((d + 1) :: R').
            -- For target M (1 :: L_2s) 5 R: L_2s = [], c' + 2 = 5 → c' = 3,
            -- R = (d + 1) :: R'. Predecessor cfg_pre = M [] 7 (d :: R').
            -- Strategy: cfg_pre.phi = cfg.phi and cfg_pre.mr < cfg.mr (D5
            -- backward decreases mr by 1). Use mk_M_empty_7 to put
            -- cfg_pre in InCascade, then apply ih_mr.
            injection htgt with hL hc hR
            injection hL with _ h_L_2s
            -- h_L_2s : [] = L_2s
            have h_L_2s' : L_2s = [] := h_L_2s
            subst h_L_2s'
            have hc' : c' = 3 := by omega
            subst hc'
            subst hR
            subst hcfg
            refine ih_mr (MacroConfig.M [] 7 (d :: R')).mr ?_
              (MacroConfig.M [] 7 (d :: R')) ?_ rfl
              (InCascade.mk_M_empty_7 (d :: R')) h_prev
            · -- mr decrease: macroMr (d :: R') < macroMr ((d+1) :: R')
              simp only [MacroConfig.mr_M, macroMr, macroPoly2_cons]
              omega
            · -- phi same: (M [] 7 (d :: R')).phi = (M [1] 5 ((d+1) :: R')).phi
              simp only [MacroConfig.phi_M,
                List.sum_cons, List.sum_nil]
              omega
          · -- D6 era_and_sweep: target M ((b + 1) :: L') (a + 4) [1].
            -- For target M (1 :: L_2s) 5 R: b + 1 = 1 → b = 0. But cfg_pre's
            -- L = (a+1) :: b :: L' has b ≥ 1 from AllGe1. ⊥.
            injection htgt with hL _ _
            injection hL with hh _
            subst hcfg
            have h_AllGe1_L := h_prev.macroInvariant.1
            -- cfg_pre = M0 ((a+1) :: b :: L') [1]. AllGe1 on L gives b ≥ 1.
            have hb := (AllGe1_cons.mp (AllGe1_cons.mp h_AllGe1_L).2).1
            omega
          · -- D7 era_and_sweep_solo (CASE B): target M [1] (a + 4) [1].
            -- For target M (1 :: L_2s) 5 R: L_2s = [], a + 4 = 5 → a = 1, R = [1].
            -- Predecessor cfg_pre = M0 [a + 1] [1] = M0 [2] [1]. Use not_M0_2_1.
            injection htgt with _ hc _
            have ha : a = 1 := by omega
            subst ha
            subst hcfg
            exact OrbitReachable.not_M0_2_1 h_prev
          · -- D8 zero_two_solo (CASE C): target M L' (a + 3) [1].
            -- For target M (1 :: L_2s) 5 R: L' = 1 :: L_2s, a + 3 = 5 → a = 2, R = [1].
            -- Predecessor cfg_pre = M0 (2 :: 1 :: L_2s) [2]. Use H2.
            injection htgt with hL hc hR
            have ha : a = 2 := by omega
            subst ha
            have hL' : L' = 1 :: L_2s := hL.symm
            subst hL'
            subst hcfg
            apply OrbitReachable.not_M0_starts_2_1_2spine_2 h_2s rfl
              (h_excl_R1_pred := fun {d} {R'_pred} h_or_pred h_phi_lt => by
                refine ih_phi (MacroConfig.M [] 3 (d :: R'_pred)).phi ?_
                  (MacroConfig.M [] 3 (d :: R'_pred)).mr
                  (MacroConfig.M [] 3 (d :: R'_pred)) rfl rfl
                  (InCascade.mk_M_empty_3 (d :: R'_pred)) h_or_pred
                simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                  List.sum_cons, List.sum_nil] at h_phi_lt ⊢
                omega)
              h_prev
          · -- D9 zero_bounce_to_zero: target M0. ⊥.
            exact MacroConfig.noConfusion htgt
          · -- D10 zero_bounce_and_shift: target M L' (a + 4) [1, 1].
            -- For target M (1 :: L_2s) 5 R: cursor a + 4 = 5 → a = 1, R = [1, 1].
            -- L' = 1 :: L_2s. Predecessor M0 (1 :: 1 :: L_2s) [4].
            injection htgt with hL hc hR
            have ha : a = 1 := by omega
            subst ha
            subst hR
            have hL' : L' = 1 :: L_2s := hL.symm
            subst hL'
            subst hcfg
            apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := L_2s)
              (r := 4) (R_rest := []) (by omega) rfl
              (h_excl_R1_pred := fun {d} {R'_pred} h_or_pred h_phi_lt => by
                refine ih_phi (MacroConfig.M [] 3 (d :: R'_pred)).phi ?_
                  (MacroConfig.M [] 3 (d :: R'_pred)).mr
                  (MacroConfig.M [] 3 (d :: R'_pred)) rfl rfl
                  (InCascade.mk_M_empty_3 (d :: R'_pred)) h_or_pred
                simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                  List.sum_cons, List.sum_nil] at h_phi_lt ⊢
                omega)
              h_prev
          · -- D11 zero_bounce: target M ((a + 4) :: L') (z + 2) [1].
            -- For target M (1 :: L_2s) 5 R: a + 4 = 1 → impossible. ⊥.
            injection htgt with hL _ _
            injection hL with hh _
            omega
          · -- D12 zero_two (CASE D): target M L' (a + 3) ((d + 1) :: R').
            -- For target M (1 :: L_2s) 5 R: L' = 1 :: L_2s, a + 3 = 5 → a = 2,
            -- R = (d + 1) :: R'. Predecessor cfg_pre = M0 (2 :: 1 :: L_2s) (2 :: d :: R').
            -- TODO: cascade chain analysis.
            sorry
        | mk_M_empty_7 R =>
          -- cfg = M [] 7 R. Backward macroStep: 4 productive predecessor
          -- shapes (D2, D8, D10, D12). 8 unproductive (D1/D3/D4/D5/D6/D7/D9/D11)
          -- close via shape contradictions. D8 closed via not_M0_4_2.
          rename_i cfg_pre _
          rcases macroStep_eq_some_cases _ _ _ h_step with
            ⟨_, _, _, _, _, _, htgt⟩
          | ⟨a, L', d, R', hcfg', _, htgt⟩  -- D2
          | ⟨_, _, _, _, _, _, _, htgt⟩
          | ⟨_, _, _, _, htgt⟩
          | ⟨_, _, _, _, _, htgt⟩
          | ⟨_, _, _, _, _, htgt⟩
          | ⟨_, _, _, htgt⟩
          | ⟨a, L', hcfg', _, htgt⟩  -- D8
          | ⟨_, _, _, _, htgt⟩
          | ⟨a10, L'10, hcfg'10, _, htgt⟩  -- D10
          | ⟨_, _, _, _, _, htgt⟩
          | ⟨_, _, _, _, _, _, htgt⟩
          -- D1: M0 target. ⊥.
          · exact MacroConfig.noConfusion htgt
          -- D2: target M L' (a+1) (1 :: ...). For target M [] 7 R: L' = [],
          -- a+1 = 7 → a = 6. R = 1 :: (d+1) :: R'. Pred M [6] 3 (d :: R').
          -- Use not_M_6_3_dR_via_ih with callback to ih_phi at mk_M_empty_3 (smaller phi).
          · injection htgt with hL hc hR
            have ha : a = 6 := by omega
            subst ha
            have hL' : L' = [] := hL.symm
            subst hL'
            subst hcfg'
            apply OrbitReachable.not_M_6_3_dR_via_ih (d := d) (R' := R') rfl
              (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
                refine ih_phi (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi ?_
                  (MacroConfig.M [] 3 (d_pre :: R'_pre)).mr
                  (MacroConfig.M [] 3 (d_pre :: R'_pre)) rfl rfl
                  (InCascade.mk_M_empty_3 (d_pre :: R'_pre)) h_or_pre
                rw [hR]
                simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
                omega)
              h_prev
          -- D3: target M ((a+1) :: L') ... cons L vs []. ⊥.
          · injection htgt with hL _ _
            exact (List.cons_ne_nil _ _) hL.symm
          -- D4: M0 target. ⊥.
          · exact MacroConfig.noConfusion htgt
          -- D5: target M [1] ... [1] vs []. ⊥.
          · injection htgt with hL _ _
            exact (List.cons_ne_nil _ _) hL.symm
          -- D6: target M ((b+1) :: L') ... cons L vs []. ⊥.
          · injection htgt with hL _ _
            exact (List.cons_ne_nil _ _) hL.symm
          -- D7: target M [1] ... cons vs []. ⊥.
          · injection htgt with hL _ _
            exact (List.cons_ne_nil _ _) hL.symm
          -- D8: target M L' (a+3) [1]. For target M [] 7 R: L' = [], a+3 = 7 → a = 4. R = [1].
          -- Pred M0 (a :: L') [2] = M0 [4] [2]. Use not_M0_4_2.
          · injection htgt with hL hc hR
            have ha : a = 4 := by omega
            subst ha
            have hL' : L' = [] := hL.symm
            subst hL'
            subst hcfg'
            exact OrbitReachable.not_M0_4_2 rfl h_prev
          -- D9: M0 target. ⊥.
          · exact MacroConfig.noConfusion htgt
          -- D10: target M L' (a+4) [1, 1]. For target M [] 7 R: L' = [],
          -- a+4 = 7 → a = 3. R = [1, 1]. Pred M0 [3] [4]. Use not_M0_3_4.
          · injection htgt with hL hc hR
            have ha : a10 = 3 := by omega
            subst ha
            have hL' : L'10 = [] := hL.symm
            subst hL'
            subst hcfg'10
            exact OrbitReachable.not_M0_3_4 rfl h_prev
          -- D11: target M ((a+4) :: L') ... cons L vs []. ⊥.
          · injection htgt with hL _ _
            exact (List.cons_ne_nil _ _) hL.symm
          -- D12: target M L' (a+3) ((d+1) :: R'). For target M [] 7 R:
          -- L' = [], a+3 = 7 → a = 4. R = (d+1) :: R'. Pred M0 [4] (2 :: d :: R').
          -- TODO: needs M0 [4] (2 :: d :: R') exclusion helper.
          · sorry
      | @step_multi_bounce_general a r' last'' L' R_mid _ =>
        -- Output: M (R_mid.reverse ++ (r'+1) :: (a+4) :: L') (last''+2) [1].
        -- (a+4) ∈ L. By L_mem_le_2, a+4 ≤ 2 — contradicts a ≥ 0.
        have h_mem : (a + 4) ∈ R_mid.reverse ++ (r' + 1) :: (a + 4) :: L' := by
          simp [List.mem_append, List.mem_cons]
        have := h_in.L_mem_le_2 (a + 4) h_mem
        omega
      | step_multi_bounce_general_to_zero _ => cases h_in
      | @step_multi_bounce_2_and_shift a r L' _ =>
        -- Output: M ((a+4) :: L') (r+2) [1, 1]. L head a+4 ≥ 4.
        cases h_in with
        | @mk_M_2spine_3 L R₀ h_2s h_ne =>
          obtain ⟨h_head, _⟩ := h_2s; omega
      | @step_multi_bounce_2_double_shift a L' h_pred =>
        -- Output: M L' (a + 4) [1, 1, 1]. Cursor a+4 ≥ 4.
        -- mk_M_1_2spine_5: cfg = M (1 :: L_2s) 5 R₀.
        -- Unification: L' = 1 :: L_2s, a + 4 = 5 → a = 1 (Lean may solve), R₀ = [1, 1, 1].
        -- Predecessor h_pred : OrbitReachable (M0 (1 :: 1 :: L_2s) [3, 2]).
        cases h_in with
        | @mk_M_1_2spine_5 L_2s R₀ h_2s =>
          apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := L_2s)
            (r := 3) (R_rest := [2]) (by omega) rfl
            (h_excl_R1_pred := fun {d} {R'_pred} h_or_pred h_phi_lt => by
              refine ih_phi (MacroConfig.M [] 3 (d :: R'_pred)).phi ?_
                (MacroConfig.M [] 3 (d :: R'_pred)).mr
                (MacroConfig.M [] 3 (d :: R'_pred)) rfl rfl
                (InCascade.mk_M_empty_3 (d :: R'_pred)) h_or_pred
              simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                List.sum_cons, List.sum_nil] at h_phi_lt ⊢
              omega)
            h_pred
        | mk_M_empty_7 _ =>
          -- cfg = M L' (a+4) [1, 1, 1] vs M [] (c+4) R: L' = [], a = c.
          -- Predecessor h_pred : OrbitReachable (M0 [c] [3, 2]).
          -- Stubbed (requires backward exclusion of M0 [c] [3, 2]).
          sorry
      | @step_multi_bounce_3run_last_2 a r' e L' _ =>
        -- Output: M ((r'+1) :: (a+4) :: L') (e+2) [1, 1].
        cases h_in with
        | @mk_M_2spine_3 L R₀ h_2s h_ne =>
          obtain ⟨_, h_tail⟩ := h_2s
          obtain ⟨h_head, _⟩ := h_tail
          omega
        | mk_M_1_2spine_5 R₀ h_2s =>
          obtain ⟨h_head, _⟩ := h_2s; omega
      | @step_multi_bounce_last_2_general a r' m_last L' middle_init _ =>
        -- Output: M (middle_init.reverse ++ (r'+1) :: (a+4) :: L') (m_last+2) [1, 1].
        -- Same as step_multi_bounce_general: (a+4) ∈ L, contradicts L_mem_le_2.
        have h_mem : (a + 4) ∈ middle_init.reverse ++ (r' + 1) :: (a + 4) :: L' := by
          simp [List.mem_append, List.mem_cons]
        have := h_in.L_mem_le_2 (a + 4) h_mem
        omega
      | @step_R2_zero a L' h_pred =>
        -- Output: M L' (a+4) [1, 1, 1, 1].
        -- mk_M_1_2spine_5: cfg = M (1 :: L_2s) 5 R₀ → L' = 1 :: L_2s, a = 1.
        -- Predecessor: M0 (a :: L') [3, 1, 2] = M0 (1 :: 1 :: L_2s) [3, 1, 2].
        cases h_in with
        | @mk_M_1_2spine_5 L_2s R₀ h_2s =>
          apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := L_2s)
            (r := 3) (R_rest := [1, 2]) (by omega) rfl
            (h_excl_R1_pred := fun {d} {R'_pred} h_or_pred h_phi_lt => by
              refine ih_phi (MacroConfig.M [] 3 (d :: R'_pred)).phi ?_
                (MacroConfig.M [] 3 (d :: R'_pred)).mr
                (MacroConfig.M [] 3 (d :: R'_pred)) rfl rfl
                (InCascade.mk_M_empty_3 (d :: R'_pred)) h_or_pred
              simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                List.sum_cons, List.sum_nil] at h_phi_lt ⊢
              omega)
            h_pred
        | mk_M_empty_7 _ =>
          -- cfg = M L' (a+4) [1, 1, 1, 1] vs M [] (c+4) R: L' = [], a = c.
          -- Predecessor h_pred : OrbitReachable (M0 [c] [3, 1, 2]).
          -- Stubbed (requires backward exclusion of M0 [c] [3, 1, 2]).
          sorry
      | @step_R2_succ a r L' _ =>
        -- Output: M ((a+4) :: L') (r+2) [1, 1, 1]. L head a+4.
        cases h_in with
        | @mk_M_2spine_3 L R₀ h_2s h_ne =>
          obtain ⟨h_head, _⟩ := h_2s; omega
      | @step_R3 a r' e L' middle_init _ _ h_prev _ _ _ h_safe h_strict_safe h_phi_side =>
        -- h_safe : ∀ R, cfg' ≠ M [] 3 R. Closes mk_M_empty_3 directly.
        -- h_strict_safe is now 4-case (2026-05-08); derive 2-disjunct form for legacy callers.
        obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
        have h_disj_2 := strict_safe_2_disjunct_of_4cases
          (AllGe1_cons.mp h_prev.macroInvariant.1).1 h_disj
        cases h_in with
        | mk_M_empty_3 R => exact h_safe R rfl
        | @mk_M_2spine_3 L R₀ h_2s h_ne =>
          -- cfg = M L 3 R₀. Inject hcfg_M to get L_suf = L, v = 3.
          rw [MacroConfig.M.injEq] at hcfg_M
          obtain ⟨hL_eq, hv_eq, _⟩ := hcfg_M
          subst hL_eq
          subst hv_eq
          rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
          · have := h_2s.mem_eq_2 x hx; omega
          · -- v = 3 = a + 4 → a = -1, impossible (a : Nat).
            omega
        | @mk_M_1_2spine_5 L_2s R₀ h_2s =>
          -- cfg = M (1 :: L_2s) 5 R₀. Inject hcfg_M.
          rw [MacroConfig.M.injEq] at hcfg_M
          obtain ⟨hL_eq, hv_eq, _⟩ := hcfg_M
          subst hL_eq
          subst hv_eq
          rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, hL_eq⟩
          · -- ∃ x ∈ (1 :: L_2s), x ≥ 5: max ≤ 2 ⊥.
            rcases List.mem_cons.mp hx with rfl | hx_tail
            · omega
            · have := h_2s.mem_eq_2 x hx_tail; omega
          · -- v = 5 = a + 4 → a = 1. L_suf = L', so L' = 1 :: L_2s.
            -- Predecessor M0 (a :: L') (...) = M0 (1 :: 1 :: L_2s) ((r'+3) :: ...).
            -- Apply M0 backward chase helper, supplying the predecessor exclusion
            -- via cascade IH (ih_phi at InCascade.mk_M_empty_3).
            have ha_eq : a = 1 := by omega
            apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := L_2s)
              (r := r' + 3) (R_rest := e :: middle_init ++ [1, 2])
              (by omega)
              (by rw [ha_eq] at h_prev ⊢; rw [← hL_eq] at h_prev ⊢; rfl)
              (h_excl_R1_pred := fun {d} {R'_pred} h_or_pred h_phi_lt => by
                -- Compute helper.cfg.phi = outer.phi - 2 explicitly via h_phi_side
                -- (after substituting a = 1 and L' = 1 :: L_2s).
                have h_phi_outer :
                    (MacroConfig.M (1 :: L_2s) 5 R₀).phi =
                    (MacroConfig.M0 (1 :: 1 :: L_2s)
                      ((r' + 3) :: e :: middle_init ++ [1, 2])).phi + 2 := by
                  have h := h_phi_side
                  rw [ha_eq, ← hL_eq] at h
                  exact h
                refine ih_phi (MacroConfig.M [] 3 (d :: R'_pred)).phi ?_
                  (MacroConfig.M [] 3 (d :: R'_pred)).mr
                  (MacroConfig.M [] 3 (d :: R'_pred)) rfl rfl
                  (InCascade.mk_M_empty_3 (d :: R'_pred)) h_or_pred
                omega)
              h_prev
        | mk_M_empty_7 R =>
          -- cfg = M [] 7 R. cfg' = cfg, so L_suf = [], v = 7. 4-case:
          -- Cases 1, 2, 3: L_suf nonempty vs []. ⊥.
          -- Case 4: a+4 = 7 (a=3), L'=[], r'=0, e=1, middle_init all 1s.
          -- Pred = M0 [3] (3 :: 1 :: middle_init ++ [1, 2]). Parametric — SORRY.
          rw [MacroConfig.M.injEq] at hcfg_M
          obtain ⟨hL_eq, hv_eq, hR_eq⟩ := hcfg_M
          subst hL_eq
          subst hv_eq
          subst hR_eq
          rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
            ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, _, _⟩
          · -- Case 1: |L_suf|=0 < 3 ⊥.
            have h_len :
                (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length =
                ([] : List Nat).length := by
              rw [← hLsuf]
            simp [List.length_append, List.length_cons] at h_len
          · -- Case 2: L_suf = (r'+1)::(a+4)::L' = []. ⊥.
            exact absurd hLsuf.symm (List.cons_ne_nil _ _)
          · -- Case 3: L_suf = (a+4)::L' = []. ⊥.
            exact absurd hLsuf.symm (List.cons_ne_nil _ _)
          · -- Case 4: a+4=7 (a=3), L'=[], r'=0, e=1, middle_init all 1s.
            -- Pred = M0 [3] (3 :: 1 :: middle_init ++ [1, 2]).
            -- Closes via chain helpers: not_M0_3_for_X_via_ih.
            rename_i h_mi_one h_e h_r hav hLsuf
            have ha : a = 3 := by omega
            have hL' : L' = [] := hLsuf.symm
            subst ha
            subst hL'
            subst h_e
            subst h_r
            apply OrbitReachable.not_M0_3_for_X_via_ih middle_init (by rfl)
              (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pred h_phi_lt => by
                refine ih_phi (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi ?_
                  (MacroConfig.M [] 3 (d_pre :: R'_pre)).mr
                  (MacroConfig.M [] 3 (d_pre :: R'_pre)) rfl rfl
                  (InCascade.mk_M_empty_3 (d_pre :: R'_pre)) h_or_pred
                simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                  List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt h_phi_side ⊢
                omega)
              h_prev
      | @step_R1 d_pre R'_pre _ _ h_pred _ _ _ h_phi =>
        -- predecessor M [] 3 (d_pre :: R'_pre). cfg.phi ≥ pred.phi + 2.
        -- Recurse via ih_phi at smaller phi.
        have h_in_pre := InCascade.mk_M_empty_3 (d_pre :: R'_pre)
        have h_pred_phi : (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi := by
          omega
        exact ih_phi (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi h_pred_phi
          (MacroConfig.M [] 3 (d_pre :: R'_pre)).mr (MacroConfig.M [] 3 (d_pre :: R'_pre))
          rfl rfl h_in_pre h_pred

/-- Top-level cascade closure: drops the explicit phi/mr arguments. -/
theorem cascade_strong (cfg : MacroConfig)
    (h_in : InCascade cfg) (h_or : OrbitReachable cfg) : False :=
  cascade_strong_aux cfg.phi cfg.mr cfg rfl rfl h_in h_or

/-- **Corollary**: M [] 3 R is never orbit-reachable. -/
theorem OrbitReachable.not_M_empty_3_via_cascade
    {cfg : MacroConfig} (h : OrbitReachable cfg) :
    ∀ R, cfg ≠ .M [] 3 R := by
  intro R hcfg
  apply cascade_strong cfg _ h
  rw [hcfg]
  exact InCascade.mk_M_empty_3 R

end Sweeper
