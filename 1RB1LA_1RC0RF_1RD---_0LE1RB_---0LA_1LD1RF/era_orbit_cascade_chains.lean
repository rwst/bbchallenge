/-
**Cascade chain helpers (Session 6, 2026-05-07)** — extracted from
`era_orbit_cascade.lean` to keep main file manageable.

Contains 22 chain helpers + the bridging `not_M_6_3_dR_via_ih`:

- D11 chain (8): `not_M0_2_2`, `not_M_empty_5_1`, `not_M_1_3_2`,
  `not_M_empty_2_1_3`, `not_M0_1_2_3`, `not_M_empty_4_4_via_ih`,
  `not_M_1_2_5_via_ih`, `not_M0_2_6_via_ih`.
- mb2as chain (7): `not_M_2_1_3_1`, `not_M_1_3_1_2`,
  `not_M_empty_2_1_2_2`, `not_M0_1_2_2_2`, `not_M_empty_4_3_2_via_ih`,
  `not_M_1_2_4_2_via_ih`, `not_M0_2_5_2_via_ih`.
- R2_succ chain (6): `not_M_1_3_1_1_2_via_ih`,
  `not_M_empty_2_1_2_1_2_via_ih`, `not_M0_1_2_2_1_2_via_ih`,
  `not_M_empty_4_3_1_2_via_ih`, `not_M_1_2_4_1_2_via_ih`,
  `not_M0_2_5_1_2_via_ih`.
- Bridge (1): `not_M_6_3_dR_via_ih` — has 3 remaining sub-sorries
  for D2, D3, step_R3 sub-cases.

Future work for closing the 3 remaining sub-sorries should add new
chain helpers to a dedicated file (e.g., `era_orbit_cascade_d2.lean`).
-/

import era_orbit_cascade

namespace Sweeper

open BusyLean

/-- **`M0 [2] [2]` is not orbit-reachable**: phi = 4 < 6 via `not_phi_lt_six`. -/
theorem OrbitReachable.not_M0_2_2 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  rw [hcfg] at h_or
  refine OrbitReachable.not_phi_lt_six ?_ h_or
  simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
  omega

/-- **`M [] 5 [1]` is not orbit-reachable**: phi = 6, D8 backward pred
    `M0 [2] [2]` excluded by `not_M0_2_2`; step_R1 self-contained at phi=6. -/
theorem OrbitReachable.not_M_empty_5_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [] 5 [1]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨a, L', hcfg', _, htgt⟩  -- D8
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩  -- D12
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R length ≥ 2 ⊥
    · mc_dcase_close
    -- D3: cons L vs [] ⊥
    · mc_dcase_close
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5,D6,D7: cons L vs [] ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D8 (productive): pred M0 [2] [2] via not_M0_2_2.
    · injection htgt with hL hc _
      have ha : a = 2 := by omega
      subst ha
      have hL' : L' = [] := hL.symm
      subst hL'
      subst hcfg'
      exact OrbitReachable.not_M0_2_2 rfl h_prev
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: R length ≥ 2 ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12 (productive): pred M0 (2::0::R') violates AllGe1.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hd : d12 = 0 := by omega
      subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have h2 := (AllGe1_cons.mp hAR).2
      have ha := (AllGe1_cons.mp h2).1
      omega
  | step_multi_bounce_general _ =>
    -- output L = R_mid.reverse ++ ... ≠ []. Length argument.
    mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    -- output L = middle_init.reverse ++ ... ≠ []. Length argument.
    mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf = [], v = 5. h_disj first: ⊥. Second: v = a+4 = 5 → a = 1, pred.phi ≥ 9, but cfg.phi = 6 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, hR_eq⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, hL_eq⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 1 := by omega
      subst ha
      have hL'' : L' = [] := hL_eq.symm
      subst hL''
      subst hR_eq
      subst hcfg_M
      simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
        List.sum_append, List.sum_cons, List.sum_nil] at h_phi_side
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [1] 3 [2]` is not orbit-reachable**: phi = 6, D5 backward pred
    `M [] 5 [1]` excluded; step_R1 self-contained. -/
theorem OrbitReachable.not_M_1_3_2 {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 3 [2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩  -- D2
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩  -- D5
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R head 1 vs 2 ⊥
    · mc_dcase_close
    -- D3 (productive): a3 = 0, AllGe1 ⊥.
    · rename_i a3 c'3 L'3 d3 R'3 hcfg'3 _
      injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5 (productive): pred M [] 5 [1].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 1 := by omega
      have hd : d5 = 1 := by omega
      have hR' : R'5 = [] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      exact OrbitReachable.not_M_empty_5_1 rfl h_prev
    -- D6, D7: cursor a+4=3 ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D8 (productive): a8 = 0, AllGe1 ⊥.
    · rename_i a8 L'8 hcfg'8 _
      injection htgt with _ hc _
      have ha : a8 = 0 := by omega
      subst ha
      subst hcfg'8
      mc_AllGe1_a_ge1
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D11: a+4 = 1 ⊥
    · mc_dcase_close
    -- D12 (productive): a12 = 0, AllGe1 ⊥.
    · rename_i a12 L'12 d12 R'12 hcfg'12 _
      injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [1], v = 3. h_disj first: 1 ≥ 5 ⊥. Second: v = a+4 = 3 → a = -1 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [] 2 [1, 3]` is not orbit-reachable**: phi = 6, D2 backward pred
    `M [1] 3 [2]` excluded; step_R1 self-contained. -/
theorem OrbitReachable.not_M_empty_2_1_3 {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 [1, 3]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2 (productive): pred M [1] 3 [2].
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR'
      have ha : a2 = 1 := by omega
      have hd : d2 = 2 := by omega
      have hL' : L'2 = [] := hL.symm
      have hR'' : R'2 = [] := hR'.symm
      subst ha
      subst hd
      subst hL'
      subst hR''
      subst hcfg'2
      exact OrbitReachable.not_M_1_3_2 rfl h_prev
    -- D3, D5, D6, D7: cons L vs nil ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D8: cursor a+3=2 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: cursor a+3=2 ⊥
    · mc_dcase_close
  | step_multi_bounce_general _ =>
    -- output L = R_mid.reverse ++ … ≠ []. Length argument.
    mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    -- output L = middle_init.reverse ++ … ≠ []. Length argument.
    mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [], v = 2. h_disj first: ⊥. Second: v = a+4 = 2 → a = -2 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M0 [1] [2, 3]` is not orbit-reachable**: phi = 6, D4 backward pred
    `M [] 2 [1, 3]` excluded; step_R1 self-contained. -/
theorem OrbitReachable.not_M0_1_2_3 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] [2, 3]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩  -- D1
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨d4, R'4, hcfg'4, _, htgt⟩  -- D4
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1 (productive): a = 0, AllGe1 ⊥.
    · injection htgt with hL hR
      injection hL with ha _
      have ha' : a = 0 := by omega
      subst ha'
      subst hcfg'
      mc_AllGe1_a_ge1
    -- D2-D3: M target ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D4 (productive): pred M [] 2 [1, 3].
    · injection htgt with hL hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = [3] := hR_tail.symm
      subst hd
      subst hR'
      subst hcfg'4
      exact OrbitReachable.not_M_empty_2_1_3 rfl h_prev
    -- D5-D8: M target ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D9: R = [1] vs [2, 3] ⊥
    · mc_dcase_close
    -- D10-D12: M target ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    mc_noconf hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [] 4 [4]` is not orbit-reachable** (callback variant): phi = 8.
    D12 backward pred `M0 [1] [2, 3]` excluded; step_R1 callback at M [] 3 (...). -/
theorem OrbitReachable.not_M_empty_4_4_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 [4])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩  -- D12
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R head 1 vs 4 ⊥
    · mc_dcase_close
    -- D3: cons L ⊥
    · mc_dcase_close
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5-D7: cons L vs nil ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D8: R head 1 vs 4 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: R head 1 vs 4 ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12 (productive): pred M0 [1] [2, 3].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hd : d12 = 3 := by omega
      have hL' : L'12 = [] := hL.symm
      have hR' : R'12 = [] := hR_tail.symm
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'12
      exact OrbitReachable.not_M0_1_2_3 rfl h_prev
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf = [], v = 4. h_disj first: ⊥. Second: v = a+4 = 4 → a = 0. AllGe1 cfg_pre ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [1] 2 [5]` is not orbit-reachable** (callback variant): phi = 8.
    D5 backward pred `M [] 4 [4]` excluded (via callback chain); step_R1 callback. -/
theorem OrbitReachable.not_M_1_2_5_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 [5])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩  -- D2
    | ⟨_, _, _, _, _, _, _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩  -- D5
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R head 1 vs 5 ⊥
    · mc_dcase_close
    -- D3 (productive): a3 = 0 AllGe1 ⊥.
    · rename_i a3 c'3 L'3 d3 R'3 hcfg'3 _
      injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5 (productive): pred M [] 4 [4] via callback.
    · injection htgt with _ hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 4 := by omega
      have hR' : R'5 = [] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_4_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6, D7: cursor a+4=2 ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D8: cursor a+3=2 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D11: a+4 = 1 ⊥
    · mc_dcase_close
    -- D12: cursor a+3=2 ⊥
    · mc_dcase_close
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [1], v = 2. h_disj first: 1 ≥ 5 ⊥. Second: v = a+4 = 2 → a = -2 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [2] [6]` is not orbit-reachable** (callback variant): phi = 8.
    D1 backward pred `M [1] 2 [5]` excluded (via callback chain); step_R1 callback. -/
theorem OrbitReachable.not_M0_2_6_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [6])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩  -- D1
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩  -- D4
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩  -- D9
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1 (productive): pred M [1] 2 [5] via callback.
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 5 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      apply OrbitReachable.not_M_1_2_5_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D2-D12: M-target ⊥ via noConfusion, or M0 R/L head mismatch ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    mc_noconf hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [2, 1] 3 [1]` is not orbit-reachable**: phi = 7 (self-contained).
    All D-cases close via shape mismatch or AllGe1 ⊥; step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M_2_1_3_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [2, 1] 3 [1]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R length ⊥
    · mc_dcase_close
    -- D3 (productive): d3 = 0 AllGe1 ⊥.
    · rename_i a3 c'3 L'3 d3 R'3 hcfg'3 _
      injection htgt with _ _ hR
      injection hR with hd_eq hR_tail
      have hd : d3 = 0 := by omega
      subst hd
      subst hcfg'3
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5: L head 1 vs 2 ⊥
    · mc_dcase_close
    -- D6: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D7: L head 1 vs 2 ⊥
    · mc_dcase_close
    -- D8 (productive): a8 = 0 AllGe1 ⊥.
    · rename_i a8 L'8 hcfg'8 _
      injection htgt with _ hc _
      have ha : a8 = 0 := by omega
      subst ha
      subst hcfg'8
      mc_AllGe1_a_ge1
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D11: a+4 = 2 ⊥
    · mc_dcase_close
    -- D12 (productive): a12 = 0 AllGe1 ⊥.
    · rename_i a12 L'12 d12 R'12 hcfg'12 _
      injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ =>
    -- output L = R_mid.reverse ++ (r'+1) :: (a+4) :: L' = [2, 1]. (a+4) ∈ L: a+4 ≥ 4 ⊥.
    rename_i a r' last'' L' R_mid _
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_mem : (a + 4) ∈ R_mid.reverse ++ (r' + 1) :: (a + 4) :: L' := by
      simp [List.mem_append, List.mem_cons]
    rw [hL] at h_mem
    rcases List.mem_cons.mp h_mem with h | h
    · omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · exact absurd h List.not_mem_nil
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [2, 1], v = 3. h_disj first: 2≥5 ⊥, 1≥5 ⊥. Second: a+4=3 → a=-1 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · rcases List.mem_cons.mp hx_tail with rfl | hx_tail2
        · omega
        · exact absurd hx_tail2 List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [1] 3 [1, 2]` is not orbit-reachable**: phi = 7. D2 → `M [2, 1] 3 [1]`. -/
theorem OrbitReachable.not_M_1_3_1_2 {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 3 [1, 2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2 (productive): pred M [2, 1] 3 [1].
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR'
      have ha : a2 = 2 := by omega
      have hd : d2 = 1 := by omega
      have hL' : L'2 = [1] := hL.symm
      have hR'' : R'2 = [] := hR'.symm
      subst ha
      subst hd
      subst hL'
      subst hR''
      subst hcfg'2
      exact OrbitReachable.not_M_2_1_3_1 rfl h_prev
    -- D3 (productive): a3 = 0 AllGe1 ⊥.
    · rename_i a3 c'3 L'3 d3 R'3 hcfg'3 _
      injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5 (productive): d5 = 0 AllGe1 ⊥.
    · rename_i c'5 d5 R'5 hcfg'5 _
      injection htgt with _ hc hR
      injection hR with hd_eq _
      have hd : d5 = 0 := by omega
      subst hd
      subst hcfg'5
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D6, D7: cursor a+4=3 ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D8 (productive): a8 = 0 AllGe1 ⊥.
    · rename_i a8 L'8 hcfg'8 _
      injection htgt with _ hc _
      have ha : a8 = 0 := by omega
      subst ha
      subst hcfg'8
      mc_AllGe1_a_ge1
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D11: a+4 = 1 ⊥
    · mc_dcase_close
    -- D12 (productive): a12 = 0 AllGe1 ⊥.
    · rename_i a12 L'12 d12 R'12 hcfg'12 _
      injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [] 2 [1, 2, 2]` is not orbit-reachable**: phi = 7. D2 → `M [1] 3 [1, 2]`. -/
theorem OrbitReachable.not_M_empty_2_1_2_2 {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 [1, 2, 2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2 (productive): pred M [1] 3 [1, 2].
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR'
      have ha : a2 = 1 := by omega
      have hd : d2 = 1 := by omega
      have hL' : L'2 = [] := hL.symm
      have hR'' : R'2 = [2] := hR'.symm
      subst ha
      subst hd
      subst hL'
      subst hR''
      subst hcfg'2
      exact OrbitReachable.not_M_1_3_1_2 rfl h_prev
    -- D3-D7: cons L vs [] (D4 is M0)
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D8: cursor a+3=2 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: cursor a+3=2 ⊥
    · mc_dcase_close
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M0 [1] [2, 2, 2]` is not orbit-reachable**: phi = 7 (self-contained),
    D1 backward → AllGe1 ⊥; D4 → `M [] 2 [1, 2, 2]` excluded; step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M0_1_2_2_2 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] [2, 2, 2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩  -- D1
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩  -- D4
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩  -- D9
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1 (productive): a = 0 AllGe1 ⊥.
    · injection htgt with hL hR
      injection hL with ha _
      have ha' : a = 0 := by omega
      subst ha'
      subst hcfg'
      mc_AllGe1_a_ge1
    -- D2-D3: M target ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D4 (productive): pred M [] 2 [1, 2, 2].
    · rename_i d4 R'4 hcfg'4 _
      injection htgt with hL hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = [2, 2] := hR_tail.symm
      subst hd
      subst hR'
      subst hcfg'4
      exact OrbitReachable.not_M_empty_2_1_2_2 rfl h_prev
    -- D5-D8: M target ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D9: R = [1] vs [2, 2, 2] ⊥
    · mc_dcase_close
    -- D10-D12: M target ⊥
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    mc_noconf hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [] 4 [3, 2]` is not orbit-reachable** (callback variant): phi = 9.
    D12 → `M0 [1] [2, 2, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M_empty_4_3_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 [3, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R head 1 vs 3 ⊥
    · mc_dcase_close
    -- D3, D5, D6, D7, D11: cons L vs [] (D4, D9 are M0)
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D8: R head 1 vs 3 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: R head 1 vs 3 ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12 (productive): pred M0 [1] [2, 2, 2].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hd : d12 = 2 := by omega
      have hL' : L'12 = [] := hL.symm
      have hR' : R'12 = [2] := hR_tail.symm
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'12
      exact OrbitReachable.not_M0_1_2_2_2 rfl h_prev
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf = [], v = 4. h_disj first ⊥. Second: a = 0. AllGe1 cfg_pre ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [1] 2 [4, 2]` is not orbit-reachable** (callback variant): phi = 9.
    D5 → `M [] 4 [3, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M_1_2_4_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 [4, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩  -- D5
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2: R head 1 vs 4 ⊥
    · mc_dcase_close
    -- D3 (productive): a3 = 0 AllGe1 ⊥.
    · rename_i a3 c'3 L'3 d3 R'3 hcfg'3 _
      injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5 (productive): pred M [] 4 [3, 2] via callback.
    · injection htgt with _ hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 3 := by omega
      have hR' : R'5 = [2] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_3_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6, D7: cursor a+4=2 ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D8: cursor a+3=2 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D11: a+4 = 1 ⊥
    · mc_dcase_close
    -- D12: cursor a+3=2 ⊥
    · mc_dcase_close
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [1], v = 2. h_disj first: 1 ≥ 5 ⊥. Second: a+4=2 → a=-2 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [2] [5, 2]` is not orbit-reachable** (callback variant): phi = 9.
    D1 → `M [1] 2 [4, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M0_2_5_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [5, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1 (productive): pred M [1] 2 [4, 2] via callback.
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 4 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [2] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      apply OrbitReachable.not_M_1_2_4_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D2-D12: M-target ⊥ via noConfusion or M0 R/L head mismatch.
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    mc_noconf hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [1] 3 [1, 1, 2]` is not orbit-reachable** (callback variant): phi = 8.
    All D-cases AllGe1 ⊥ or shape ⊥; step_R1 callback. -/
theorem OrbitReachable.not_M_1_3_1_1_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 3 [1, 1, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩  -- D5
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨a8, L'8, hcfg'8, _, htgt⟩  -- D8
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩  -- D12
    -- D1: M0 ⊥
    · mc_dcase_close
    -- D2 (productive): d2 = 0 AllGe1 ⊥.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3 (productive): a3 = 0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · mc_dcase_close
    -- D5 (productive): d5 = 0 AllGe1 ⊥.
    · injection htgt with _ hc hR
      injection hR with hd_eq _
      have hd : d5 = 0 := by omega
      subst hd
      subst hcfg'5
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D6, D7: cursor a+4=3 ⊥
    · mc_dcase_close
    · mc_dcase_close
    -- D8 (productive): a8 = 0 AllGe1 ⊥.
    · injection htgt with _ hc _
      have ha : a8 = 0 := by omega
      subst ha
      subst hcfg'8
      mc_AllGe1_a_ge1
    -- D9: M0 ⊥
    · mc_dcase_close
    -- D10: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D11: a+4 = 1 ⊥
    · mc_dcase_close
    -- D12 (productive): a12 = 0 AllGe1 ⊥.
    · injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ => mc_rule_close
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [] 2 [1, 2, 1, 2]` is not orbit-reachable** (callback variant): phi = 8.
    D2 → `M [1] 3 [1, 1, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M_empty_2_1_2_1_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 [1, 2, 1, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: L'=[]. a+1=2 (a=1). R=[1, 2, 1, 2]=1::(d+1)::R'' → d=1, R''=[1, 2].
    -- Pred M [1] 3 [1, 1, 2]. Use not_M_1_3_1_1_2_via_ih.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR'
      have ha : a2 = 1 := by omega
      have hd : d2 = 1 := by omega
      have hL' : L'2 = [] := hL.symm
      have hR'' : R'2 = [1, 2] := hR'.symm
      subst ha
      subst hd
      subst hL'
      subst hR''
      subst hcfg'2
      apply OrbitReachable.not_M_1_3_1_1_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D3: cons L vs [] ⊥
    · mc_dcase_close
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: [1] vs [] ⊥
    · mc_dcase_close
    -- D6: cons L ⊥
    · mc_dcase_close
    -- D7: [1] vs [] ⊥
    · mc_dcase_close
    -- D8: cursor a+3=2 → a=-1 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: cursor a+3=2 → a=-1 ⊥
    · mc_dcase_close
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    mc_rule_close
  | step_multi_bounce_2_double_shift _ =>
    mc_rule_close
  | step_multi_bounce_3run_last_2 _ =>
    mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ =>
    mc_rule_close
  | step_R2_succ _ =>
    mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [1] [2, 2, 1, 2]` is not orbit-reachable** (callback variant): phi = 8.
    D1 → AllGe1 ⊥; D4 → `M [] 2 [1, 2, 1, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M0_1_2_2_1_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] [2, 2, 1, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨d4, R'4, hcfg'4, _, htgt⟩  -- D4
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: a+1=1 → a=0 AllGe1 ⊥
    · injection htgt with hL hR
      injection hL with ha _
      have ha' : a = 0 := by omega
      subst ha'
      subst hcfg'
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] ((d+1) :: R'). [1] match. R = [2, 2, 1, 2] = (d+1) :: R'' → d=1, R''=[2, 1, 2].
    · injection htgt with _ hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = [2, 1, 2] := hR_tail.symm
      subst hd
      subst hR'
      subst hcfg'4
      apply OrbitReachable.not_M_empty_2_1_2_1_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: R = [1] vs [2, 2, 1, 2] ⊥
    · injection htgt with _ hR
      injection hR with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    mc_rule_close
  | step_multi_bounce_2_and_shift _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_double_shift _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_3run_last_2 _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_last_2_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_R2_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_R2_succ _ =>
    exact MacroConfig.noConfusion hcfg
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [] 4 [3, 1, 2]` is not orbit-reachable** (callback variant): phi = 10.
    D12 → `M0 [1] [2, 2, 1, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M_empty_4_3_1_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 [3, 1, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: a+1=4 (a=3). R=[3, 1, 2] = 1 :: ... head 1 vs 3 ⊥
    · mc_dcase_close
    -- D3: cons L ⊥
    · mc_dcase_close
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: [1] vs [] ⊥
    · mc_dcase_close
    -- D6: cons L ⊥
    · mc_dcase_close
    -- D7: [1] vs [] ⊥
    · mc_dcase_close
    -- D8: R=[1] vs [3, 1, 2] ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: R=[1, 1] vs [3, 1, 2] ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: L'=[]. a+3=4 (a=1). R=[3, 1, 2]=(d+1)::R'' → d=2, R''=[1, 2].
    -- Pred M0 [1] [2, 2, 1, 2].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hd : d12 = 2 := by omega
      have hL' : L'12 = [] := hL.symm
      have hR' : R'12 = [1, 2] := hR_tail.symm
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_1_2_2_1_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    mc_rule_close
  | step_multi_bounce_2_double_shift _ =>
    mc_rule_close
  | step_multi_bounce_3run_last_2 _ =>
    mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ =>
    mc_rule_close
  | step_R2_succ _ =>
    mc_rule_close
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [1] 2 [4, 1, 2]` is not orbit-reachable** (callback variant): phi = 10.
    D5 → `M [] 4 [3, 1, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M_1_2_4_1_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 [4, 1, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩  -- D5
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: R = [4, 1, 2] = 1 :: ... head 1 vs 4 ⊥
    · mc_dcase_close
    -- D3: a+1 = 1 → a = 0 AllGe1 ⊥
    · injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: c'+2=2 (c'=0). (d+1)::R'=[4, 1, 2] → d=3, R'=[1, 2]. Pred M [] 4 [3, 1, 2].
    · injection htgt with _ hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 3 := by omega
      have hR' : R'5 = [1, 2] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_3_1_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D7: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D8: cursor a+3=2 → a=-1 ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 ⊥
    · mc_dcase_close
    -- D11: (a+4) :: L' = [1] → a+4=1 ⊥
    · mc_dcase_close
    -- D12: cursor a+3=2 → a=-1 ⊥
    · mc_dcase_close
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    mc_rule_close
  | step_multi_bounce_2_double_shift _ =>
    mc_rule_close
  | step_multi_bounce_3run_last_2 _ =>
    mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ =>
    mc_rule_close
  | step_R2_succ _ =>
    mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [2] [5, 1, 2]` is not orbit-reachable** (callback variant): phi = 10.
    D1 → `M [1] 2 [4, 1, 2]` excluded; step_R1 callback. -/
theorem OrbitReachable.not_M0_2_5_1_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [5, 1, 2])
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: a+1=2 (a=1), L'=[]. d+1=5 (d=4), R'=[1, 2]. Pred M [1] 2 [4, 1, 2].
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 4 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [1, 2] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      apply OrbitReachable.not_M_1_2_4_1_2_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: [1] vs [2] ⊥
    · injection htgt with hL _
      injection hL with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: R=[1] vs [5, 1, 2] ⊥
    · injection htgt with _ hR
      injection hR with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    mc_rule_close
  | step_multi_bounce_2_and_shift _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_double_shift _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_3run_last_2 _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_last_2_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_R2_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_R2_succ _ =>
    exact MacroConfig.noConfusion hcfg
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback



end Sweeper
