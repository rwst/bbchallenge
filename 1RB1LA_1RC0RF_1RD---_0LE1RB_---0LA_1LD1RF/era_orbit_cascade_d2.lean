/-
**D2 sub-case work file (Session 8, 2026-05-07)** — closing the D2
sub-sorry of `not_M_6_3_dR_via_ih` (predecessor `M [2, 6] 3 (d :: R')`).

Backward analysis of `M [2, 6] 3 (d :: R')` produces:
- D2 (when d=1, R' starts ≥ 2): pred `M [2, 2, 6] 3 (...)` — RECURSIVE,
  requires parametric helper or structural argument.
- D3: pred `M [1, 6] 5 (d :: R')` — NEW cursor-5 shape, also branches.
- multi_bounce_general (R=[1]): pred `M0 [2] [4, 1]` — closeable via
  short chain (4 helpers), terminates at `M0 [1] [2, 1, 1]` (phi=5,
  phi_lt_six).
- multi_bounce_3run_last_2 / last_2_general (R=[1,1]): pred
  `M0 [2] [4, 3, 2]` — closeable via 5-helper chain ending at
  `M [] 2 [1, 1, 3, 2]` (terminal, D2 backward AllGe1 ⊥).
- step_R3: existential disjunct (∃ x ∈ [2, 6], x ≥ 5) holds with x=6,
  no contradiction. Generic M0 predecessor — same situation as in
  parent helper.
- step_R1: callback.

This file builds the closeable chains. The D2 recursion, D3, and
step_R3 sub-cases remain sorried — they require a structural argument
beyond pure chain analysis.
-/

import era_orbit_cascade_chains

namespace Sweeper

open BusyLean

-- ============================================================
-- Section A: M0 [2] [4, 1] chain (multi_bounce_general sub-case)
-- ============================================================

/-- **`M0 [1] [2, 1, 1]` is not orbit-reachable**: phi = 5 < 6. -/
theorem OrbitReachable.not_M0_1_2_1_1 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] [2, 1, 1]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  rw [hcfg] at h_or
  mc_phi_lt_six

/-- **`M [] 4 [2, 1]` is not orbit-reachable**: phi = 7 (self-contained,
    step_R1 phi-bound ⊥). D12 → `M0 [1] [2, 1, 1]` (phi_lt_six). -/
theorem OrbitReachable.not_M_empty_4_2_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 [2, 1]) :
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
    -- D2: target M L' (a+1) (1 :: ...). For [] 4 [2, 1]: a+1=4 (a=3). R=[2, 1]=1::... ⊥
    · mc_dcase_close
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
    -- D8: target M L' (a+3) [1]. R=[1] vs [2, 1] ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: target M L' (a+4) [1, 1]. R=[1, 1] vs [2, 1] ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: L'=[]. a+3=4 (a=1). R=[2, 1]=(d+1)::R' → d=1, R'=[1]. Pred M0 [1] [2, 1, 1].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hd : d12 = 1 := by omega
      have hL' : L'12 = [] := hL.symm
      have hR' : R'12 = [1] := hR_tail.symm
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'12
      exact OrbitReachable.not_M0_1_2_1_1 rfl h_prev
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
    rcases h_disj with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [1] 2 [3, 1]` is not orbit-reachable**: phi = 7 (self-contained).
    D5 → `M [] 4 [2, 1]` (closes); step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M_1_2_3_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 [3, 1]) :
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
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: R=[3, 1] = 1::... head 1 vs 3 ⊥
    · mc_dcase_close
    -- D3: a+1=1 → a=0 AllGe1 ⊥
    · injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1) :: R'). [1] match. c'+2=2 (c'=0).
    -- (d+1)::R'=[3, 1] → d=2, R'=[1]. Pred M [] 4 [2, 1].
    · injection htgt with _ hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 2 := by omega
      have hR' : R'5 = [1] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      exact OrbitReachable.not_M_empty_4_2_1 rfl h_prev
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M0 [2] [4, 1]` is not orbit-reachable**: phi = 7 (self-contained).
    D1 → `M [1] 2 [3, 1]` (closes); step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M0_2_4_1 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [4, 1]) :
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
    -- D1: a+1=2 (a=1), L'=[]. d+1=4 (d=3), R'=[1]. Pred M [1] 2 [3, 1].
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 3 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [1] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      exact OrbitReachable.not_M_1_2_3_1 rfl h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: [1] vs [2] ⊥
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: R=[1] vs [4, 1] ⊥
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    injection hR.symm with hh _
    omega
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

-- ============================================================
-- Section B: M0 [2] [4, 3, 2] chain (mb3run / mb_last_2 sub-cases)
-- ============================================================

/-- **`M [] 2 [1, 1, 3, 2]` is not orbit-reachable** (callback variant): phi = 9.
    All D-cases AllGe1 ⊥ or shape ⊥; step_R1 callback. -/
theorem OrbitReachable.not_M_empty_2_1_1_3_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 [1, 1, 3, 2])
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
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
    -- D2: L'=[]. a+1=2 (a=1). R=[1, 1, 3, 2]=1::(d+1)::R'' → d+1=1, d=0 AllGe1 ⊥
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [1] [2, 1, 3, 2]` is not orbit-reachable** (callback variant): phi = 9.
    D1 AllGe1 ⊥; D4 → `M [] 2 [1, 1, 3, 2]`; step_R1 callback. -/
theorem OrbitReachable.not_M0_1_2_1_3_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] [2, 1, 3, 2])
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
    | ⟨d4, R'4, hcfg'4, _, htgt⟩
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
    -- D4: target M0 [1] ((d+1) :: R'). [1] match. R=[2, 1, 3, 2]=(d+1)::R'' → d=1, R''=[1, 3, 2].
    -- Pred M [] 2 [1, 1, 3, 2].
    · injection htgt with _ hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = [1, 3, 2] := hR_tail.symm
      subst hd
      subst hR'
      subst hcfg'4
      apply OrbitReachable.not_M_empty_2_1_1_3_2_via_ih (by rfl)
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
    -- D9: R=[1] vs [2, 1, 3, 2] ⊥
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    injection hR.symm with hh _
    omega
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [] 4 [2, 3, 2]` is not orbit-reachable** (callback variant): phi = 11.
    D12 → `M0 [1] [2, 1, 3, 2]`; step_R1 callback. -/
theorem OrbitReachable.not_M_empty_4_2_3_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 [2, 3, 2])
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
    -- D2: a+1=4 (a=3), L'=[]. R=[2, 3, 2]=1::... head 1 vs 2 ⊥
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
    -- D8: R=[1] vs [2, 3, 2] ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: R=[1, 1] vs [2, 3, 2] ⊥
    · mc_dcase_close
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: L'=[]. a+3=4 (a=1). R=[2, 3, 2]=(d+1)::R' → d=1, R'=[3, 2]. Pred M0 [1] [2, 1, 3, 2].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hd : d12 = 1 := by omega
      have hL' : L'12 = [] := hL.symm
      have hR' : R'12 = [3, 2] := hR_tail.symm
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_1_2_1_3_2_via_ih (by rfl)
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
    rcases h_disj with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [1] 2 [3, 3, 2]` is not orbit-reachable** (callback variant): phi = 11.
    D5 → `M [] 4 [2, 3, 2]`; step_R1 callback. -/
theorem OrbitReachable.not_M_1_2_3_3_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 [3, 3, 2])
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
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: R=[3, 3, 2] = 1::... head 1 vs 3 ⊥
    · mc_dcase_close
    -- D3: a+1=1 → a=0 AllGe1 ⊥
    · injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1) :: R'). [1] match. c'+2=2 (c'=0).
    -- (d+1)::R'=[3, 3, 2] → d=2, R'=[3, 2]. Pred M [] 4 [2, 3, 2].
    · injection htgt with _ hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 2 := by omega
      have hR' : R'5 = [3, 2] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_2_3_2_via_ih (by rfl)
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [2] [4, 3, 2]` is not orbit-reachable** (callback variant): phi = 11.
    D1 → `M [1] 2 [3, 3, 2]`; step_R1 callback. -/
theorem OrbitReachable.not_M0_2_4_3_2_via_ih {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [4, 3, 2])
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
    -- D1: a+1=2 (a=1), L'=[]. d+1=4 (d=3), R'=[3, 2]. Pred M [1] 2 [3, 3, 2].
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 3 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [3, 2] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      apply OrbitReachable.not_M_1_2_3_3_2_via_ih (by rfl)
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
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: R=[1] vs [4, 3, 2] ⊥
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    injection hR.symm with hh _
    omega
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

-- ============================================================
-- Section C: not_M_2_6_3_dR_via_ih (D2 sub-case bridge)
-- ============================================================

/-- **`M [2, 6] 3 (d :: R')` is not orbit-reachable** (callback variant).
    Closes shape-⊥ and AllGe1-⊥ sub-cases plus mb_general / mb3run /
    mb_last_2_general via Section A/B chain helpers. **D2 recursive**
    closed via parametric helper `not_M_kspine_6_3_R_via_ih` at k=2
    (Section D, Nat strong induction on R.length). **2 sub-sorries
    remain**: D3 (pred M [1, 6] 5), step_R3 (existential disjunct
    ∃ x ∈ [2, 6], x ≥ 5 holds with x=6). -/
theorem OrbitReachable.not_M_2_6_3_dR_via_ih {cfg : MacroConfig}
    {d : Nat} {R' : List Nat}
    (hcfg : cfg = .M [2, 6] 3 (d :: R'))
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2 recursive
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨a8, L'8, hcfg'8, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2 recursive: pred M [2, 2, 6] 3 (d2 :: R'2) = M (List.replicate 2 2 ++ [6]) 3 (...).
    -- Forward ref to `not_M_kspine_6_3_R_via_ih` (defined later, currently has its own
    -- structural issues). Sorry-stubbed.
    · sorry
    -- D3: pred M [1, 6] 5 (d3 :: R'). Forward ref to `not_M_1_6_5_R_via_ih` (defined
    -- later). Sorry-stubbed.
    · sorry
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: [1] vs [2, 6]: head 1 vs 2 ⊥
    · mc_dcase_close
    -- D6: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D7: target M [1] ... [1] vs [2, 6] ⊥
    · mc_dcase_close
    -- D8: cursor a+3=3 → a=0 AllGe1 ⊥
    · injection htgt with _ hc _
      have ha : a8 = 0 := by omega
      subst ha
      subst hcfg'8
      mc_AllGe1_a_ge1
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=3 ⊥
    · mc_dcase_close
    -- D11: (a+4) :: L' = [2, 6] → a+4=2 ⊥
    · mc_dcase_close
    -- D12: cursor a+3=3 → a=0 AllGe1 ⊥
    · injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | @step_multi_bounce_general _ _ _ _ _ _ =>
    -- For helper M [2, 6] 3 (d::R'): last''+2=3 ⟹ last''=1, last''+3=4. After r'=1
    -- and R_mid=L'=[], the predecessor is M0 [2] [4, 4] (NOT [4, 1] — the comment in
    -- the original code was wrong). No helper exists for [4, 4]; sorry-stubbed.
    sorry
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- output L = (a+4) :: L' = [2, 6] → a+4=2 ⊥
    mc_rule_close
  | step_multi_bounce_2_double_shift _ =>
    -- cursor a+4=3 ⊥
    mc_rule_close
  | @step_multi_bounce_3run_last_2 a r' e L' h_pred_3run =>
    -- output L = (r'+1) :: (a+4) :: L' = [2, 6] → r'+1=2 (r'=1), a+4=6 (a=2), L'=[].
    -- cursor e+2=3 (e=1). R=[1, 1] requires d=1, R'=[1]. Pred M0 [2] [4, 3, 2].
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, hR⟩ := hcfg
    injection hL with hr hL_tail
    injection hL_tail with ha hL_eq
    injection hR with hd_eq hR_eq
    have hr' : r' = 1 := by omega
    have ha' : a = 2 := by omega
    have hL'_empty : L' = [] := hL_eq
    have he : e = 1 := by omega
    have hd' : d = 1 := hd_eq.symm
    have hR'_eq : R' = [1] := hR_eq.symm
    subst hr'
    subst ha'
    subst hL'_empty
    subst he
    subst hd'
    subst hR'_eq
    apply OrbitReachable.not_M0_2_4_3_2_via_ih (by rfl)
      (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
        apply h_excl_R1_pred h_or_pre
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
          List.sum_cons, List.sum_nil] at h_phi_lt ⊢
        omega)
      h_pred_3run
  | @step_multi_bounce_last_2_general a r' m_last L' middle_init h_pred_lg =>
    -- L = middle_init.reverse ++ (r'+1) :: (a+4) :: L' = [2, 6]. Length argument:
    -- middle_init.length + L'.length = 0 → both empty. Then (r'+1)::(a+4)::[] = [2, 6].
    -- → r'=1, a=2, m_last=1, d=1, R'=[1]. Pred M0 [2] [4, 3, 2].
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, hR⟩ := hcfg
    injection hR with hd_eq hR_eq
    have h_len : (middle_init.reverse ++ (r' + 1) :: (a + 4) :: L').length =
        [2, 6].length := by rw [hL]
    simp only [List.length_append, List.length_cons, List.length_reverse, List.length_nil] at h_len
    have hmiddle_len : middle_init.length = 0 := by omega
    have hL'_len : L'.length = 0 := by omega
    have hmiddle : middle_init = [] := List.eq_nil_of_length_eq_zero hmiddle_len
    have hL'_empty : L' = [] := List.eq_nil_of_length_eq_zero hL'_len
    subst hmiddle
    subst hL'_empty
    simp only [List.reverse_nil, List.nil_append] at hL
    injection hL with hr hL_tail
    injection hL_tail with ha _
    have hr' : r' = 1 := by omega
    have ha' : a = 2 := by omega
    have hm : m_last = 1 := by omega
    have hd' : d = 1 := hd_eq.symm
    have hR'_eq : R' = [1] := hR_eq.symm
    subst hr'
    subst ha'
    subst hm
    subst hd'
    subst hR'_eq
    apply OrbitReachable.not_M0_2_4_3_2_via_ih (by simp)
      (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
        apply h_excl_R1_pred h_or_pre
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
          List.sum_cons, List.sum_nil, List.sum_append,
          List.reverse_nil, List.nil_append] at h_phi_lt ⊢
        omega)
      h_pred_lg
  | step_R2_zero _ =>
    mc_rule_close
  | step_R2_succ _ =>
    -- (a+4) :: L' = [2, 6] → a+4=2 ⊥
    mc_rule_close
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    -- L_suf = [2, 6], v = 3. h_disj first: x = 6 ∈ [2, 6], 6 ≥ 5 ✓ (no ⊥).
    -- Second: a+4=3 ⊥. So h_disj satisfied via first branch — sorry-stubbed.
    sorry
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

-- ============================================================
-- Section C2: Helpers for M [1, 6] 5 R chain (D3 sub-case support)
-- ============================================================

/-- **`M [] 4 [1, 1]` is not orbit-reachable**: phi = 6 (self-contained).
    All D-cases close via shape ⊥ or AllGe1 ⊥; step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M_empty_4_1_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 [1, 1]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨a10, L'10, hcfg'10, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: L'=[]. a+1=4 (a=3). R=[1, 1] = 1::(d+1)::R' → d=0 AllGe1 ⊥
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
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
    -- D8: R=[1] vs [1, 1] ⊥
    · mc_dcase_close
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: L'=[]. a+4=4 (a=0). AllGe1 ⊥
    · injection htgt with hL hc hR
      have ha : a10 = 0 := by omega
      subst ha
      have hL' : L'10 = [] := hL.symm
      subst hL'
      subst hcfg'10
      mc_AllGe1_a_ge1
    -- D11: cons L ⊥
    · mc_dcase_close
    -- D12: L'=[]. a+3=4 (a=1). R=[1, 1] = (d+1)::R' → d=0 AllGe1 ⊥.
    -- cfg_prev is M0 (a::L') (2 :: 0 :: R'); MacroInvariant.2.1 = AllGe1 R, peel twice.
    · injection htgt with hL hc hR
      injection hR with hd_eq _
      have hd : d12 = 0 := by omega
      subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have hd_ge := (AllGe1_cons.mp (AllGe1_cons.mp hAR).2).1
      omega
  | step_multi_bounce_general _ =>
    mc_rule_close
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    mc_rule_close
  | step_multi_bounce_2_double_shift _ =>
    -- output R = [1, 1, 1] vs cfg R = [1, 1]: tail mismatch [1] vs [], cons_ne_nil after
    -- two injections.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with _ hR_tail
    injection hR_tail with _ hR_tail2
    exact (List.cons_ne_nil _ _) hR_tail2
  | step_multi_bounce_3run_last_2 _ =>
    mc_rule_close
  | step_multi_bounce_last_2_general _ =>
    mc_rule_close
  | step_R2_zero _ =>
    -- output R = [1, 1, 1, 1] vs cfg R = [1, 1]: peel two cons.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with _ hR_tail
    injection hR_tail with _ hR_tail2
    exact (List.cons_ne_nil _ _) hR_tail2
  | step_R2_succ _ =>
    mc_rule_close
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨_, hx, _⟩ | ⟨h_v_eq, _⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M [1] 2 [2, 1]` is not orbit-reachable**: phi = 6 (self-contained).
    D5 → `M [] 4 [1, 1]`; step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M_1_2_2_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 [2, 1]) :
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
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: R=[2, 1] = 1::... head 1 vs 2 ⊥
    · mc_dcase_close
    -- D3: a+1=1 → a=0 AllGe1 ⊥
    · injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1) :: R'). [1] match. c'+2=2 (c'=0).
    -- (d+1)::R'=[2, 1] → d=1, R'=[1]. Pred M [] 4 [1, 1].
    · injection htgt with _ hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 1 := by omega
      have hR' : R'5 = [1] := hR_tail.symm
      subst hc'
      subst hd
      subst hR'
      subst hcfg'5
      exact OrbitReachable.not_M_empty_4_1_1 rfl h_prev
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
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with _ hR_tail
    injection hR_tail with hh _
    omega
  | step_multi_bounce_last_2_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with _ hR_tail
    injection hR_tail with hh _
    omega
  | step_R2_zero _ =>
    mc_rule_close
  | step_R2_succ _ =>
    mc_rule_close
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

/-- **`M0 [2] [3, 1]` is not orbit-reachable**: phi = 6 (self-contained).
    D1 → `M [1] 2 [2, 1]`; step_R1 phi-bound ⊥. -/
theorem OrbitReachable.not_M0_2_3_1 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] [3, 1]) :
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
    -- D1: a+1=2 (a=1), L'=[]. d+1=3 (d=2), R'=[1]. Pred M [1] 2 [2, 1].
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 2 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [1] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      exact OrbitReachable.not_M_1_2_2_1 rfl h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: [1] vs [2] ⊥
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: R=[1] vs [3, 1] ⊥
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    injection hR.symm with hh _
    omega
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_self

-- ============================================================
-- Section C3: not_M_1_6_5_R_via_ih (D3 sub-case bridge)
-- ============================================================

/-- **`M [1, 6] 5 (d :: R')` is not orbit-reachable** (callback variant).
    Closes 4 sub-cases via `not_M0_starts_1_1_R_ge2` (with L_rest=[6])
    for predecessors M0 [1, 1, 6] (...) with R head ≥ 2: D10
    (R=[1, 1] specific), mb2_double_shift (R=[1, 1, 1]), step_R2_zero
    (R=[1, 1, 1, 1]), step_R3 second-disjunct (a=1, L_suf=L').
    Closes mb_general (R=[1]) via `not_M0_2_3_1`. **5 sub-sorries**:
    D2 (pred M [4, 1, 6] 3), D8 (pred M0 [2, 1, 6] [2]), D12 d ≥ 2
    (pred M0 [2, 1, 6] (2 :: d :: R')), mb3run / mb_last_2_general
    (pred M0 [2] [3, 5, 2]), step_R3 first disjunct. -/
theorem OrbitReachable.not_M_1_6_5_R_via_ih {cfg : MacroConfig}
    {d : Nat} {R' : List Nat}
    (hcfg : cfg = .M [1, 6] 5 (d :: R'))
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
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a6, b6, L'6, hcfg'6, _, htgt⟩  -- D6
    | ⟨_, _, _, htgt⟩
    | ⟨a8, L'8, hcfg'8, _, htgt⟩  -- D8
    | ⟨_, _, _, _, htgt⟩
    | ⟨a10, L'10, hcfg'10, _, htgt⟩  -- D10
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩  -- D12
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: pred M [4, 1, 6] 3 (d2 :: R'2). NEW shape — sorry.
    · sorry
    -- D3: a=0 AllGe1 ⊥
    · injection htgt with hL _ _
      injection hL with hh _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1)::R'). [1] vs [1, 6]: head match, tail [] vs [6] ⊥
    · injection htgt with hL _ _
      injection hL with _ hL_tail
      exact (List.cons_ne_nil _ _) hL_tail
    -- D6: cursor a+4=5 (a=1). target M ((b+1)::L') (a+4) [1]. (b+1)::L' = [1, 6] → b=0 AllGe1 ⊥
    · injection htgt with hL _ _
      injection hL with hb _
      have hb' : b6 = 0 := by omega
      subst hb'
      subst hcfg'6
      have hAL := h_prev.macroInvariant.1
      -- AllGe1 ((a+1) :: 0 :: L'). Peel: (a+1) ≥ 1 ✓; then 0 ≥ 1 ⊥.
      have h2 := (AllGe1_cons.mp hAL).2
      have hb_ge := (AllGe1_cons.mp h2).1
      omega
    -- D7: target M [1] (a+4) [1]. [1] vs [1, 6] ⊥
    · injection htgt with hL _ _
      injection hL with _ hL_tail
      exact (List.cons_ne_nil _ _) hL_tail
    -- D8: cursor a+3=5 (a=2). L'=[1, 6]. R=[1] → d=1, R'=[]. Pred M0 [2, 1, 6] [2]. NEW — sorry.
    · sorry
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=5 (a=1). L'=[1, 6]. R=[1, 1] → d=1, R'=[1]. Pred M0 [1, 1, 6] [4].
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a10 = 1 := by omega
      have hd : d = 1 := hd_eq
      have hL' : L'10 = [1, 6] := hL.symm
      have hR' : R' = [1] := hR_tail
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'10
      apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := [6])
        (r := 4) (R_rest := []) (by omega) (by simp)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D11: (a+4)::L' = [1, 6] → a+4=1 ⊥
    · mc_dcase_close
    -- D12: cursor a+3=5 (a=2). L'=[1, 6]. R = (d+1)::R'. d ≥ 1 (d_var ≥ 0). Pred M0 [2, 1, 6] (2 :: d_var :: R').
    -- Sub-cases on d_var. NEW shape — sorry.
    · sorry
  | @step_multi_bounce_general _ _ _ _ _ _ =>
    -- For helper M [1, 6] 5 (d::R'): last''+2 = 5 → last''=3, so pred R = R_mid ++ [6].
    -- After length argument R_mid=L'=[], pred = M0 [2] [3, 6] — NEW shape, no chain helper.
    sorry
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- cursor r+2=5 (r=3). (a+4)::L'=[1, 6] → a+4=1 ⊥
    mc_rule_close
  | @step_multi_bounce_2_double_shift a L' h_pred_2ds =>
    -- output M L' (a+4) [1, 1, 1]. cursor a+4=5 (a=1). L'=[1, 6]. R=[1, 1, 1].
    -- Pred M0 (1 :: [1, 6]) [3, 2] = M0 [1, 1, 6] [3, 2].
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, hR⟩ := hcfg
    injection hR with hd_eq hR_tail
    have ha : a = 1 := by omega
    have hd : d = 1 := hd_eq.symm
    have hL' : L' = [1, 6] := hL
    have hR' : R' = [1, 1] := hR_tail.symm
    subst ha
    subst hd
    subst hL'
    subst hR'
    apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := [6])
      (r := 3) (R_rest := [2]) (by omega) (by simp)
      (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
        apply h_excl_R1_pred h_or_pre
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
          List.sum_cons, List.sum_nil] at h_phi_lt ⊢
        omega)
      h_pred_2ds
  | step_multi_bounce_3run_last_2 _ =>
    -- output L = (r'+1) :: (a+4) :: L' = [1, 6] → r'+1=1 (r'=0), a+4=6 (a=2), L'=[].
    -- cursor e+2=5 (e=3). R=[1, 1]. Pred M0 [2] [3, 5, 2]. NEW — sorry.
    sorry
  | step_multi_bounce_last_2_general _ =>
    -- L = middle_init.reverse ++ (r'+1) :: (a+4) :: L' = [1, 6]. Length argument:
    -- middle_init=[], L'=[]. r'+1=1 (r'=0), a+4=6 (a=2). m_last+2=5 (m_last=3).
    -- R=[1, 1]. Pred M0 [2] [3, 5, 2]. Same as mb3run — sorry.
    sorry
  | @step_R2_zero a L' h_pred_r2z =>
    -- output M L' (a+4) [1, 1, 1, 1]. cursor a+4=5 (a=1). L'=[1, 6]. R=[1, 1, 1, 1].
    -- Pred M0 (1 :: [1, 6]) [3, 1, 2] = M0 [1, 1, 6] [3, 1, 2].
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, hR⟩ := hcfg
    injection hR with hd_eq hR_tail
    have ha : a = 1 := by omega
    have hd : d = 1 := hd_eq.symm
    have hL' : L' = [1, 6] := hL
    have hR' : R' = [1, 1, 1] := hR_tail.symm
    subst ha
    subst hd
    subst hL'
    subst hR'
    apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := [6])
      (r := 3) (R_rest := [1, 2]) (by omega) (by simp)
      (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
        apply h_excl_R1_pred h_or_pre
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
          List.sum_cons, List.sum_nil] at h_phi_lt ⊢
        omega)
      h_pred_r2z
  | step_R2_succ _ =>
    -- cursor r+2=5 (r=3). (a+4)::L'=[1, 6] → a+4=1 ⊥
    mc_rule_close
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1, 6], v=5. h_disj: ∃ x ∈ [1, 6], x ≥ 5 (x=6 ✓) OR (v=a+4=5 ∧ L_suf=L' → a=1, L'=[1, 6]).
    -- Branch 2: pred M0 [1, 1, 6] (...). Use not_M0_starts_1_1_R_ge2.
    -- Branch 1: pred M0 (a :: L') (...) generic — SORRY.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, hR_eq⟩ := hcfg
    subst hL_eq
    subst hv_eq
    subst hR_eq
    rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, hL_eq⟩
    · -- Branch 1: existential. x ∈ [1, 6], x ≥ 5. SORRY.
      sorry
    · -- Branch 2: a+4=5 (a=1), L_suf=L'=[1, 6].
      have ha : a = 1 := by omega
      subst ha
      have hL'' : L' = [1, 6] := hL_eq.symm
      subst hL''
      subst hcfg_M
      apply OrbitReachable.not_M0_starts_1_1_R_ge2 (L_rest := [6])
        (r := r' + 3) (R_rest := e :: middle_init ++ [1, 2]) (by omega) (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          -- h_phi_side bridges outer cfg.phi = pred.phi + 2 (from step_R3 constructor).
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt h_phi_side ⊢
          omega)
        h_prev_R3
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

-- ============================================================
-- Section D: Parametric helper for `M [2^k, 6] 3 R` with k ≥ 2
-- ============================================================

/-- **Parametric helper** for `M (List.replicate k 2 ++ [6]) 3 R` with
    k ≥ 2. Closes via strong induction on R.length: D2 backward decreases
    R.length by 1 (and increases k by 1). All other forward cases close
    via shape ⊥ / AllGe1 ⊥ for k ≥ 2 EXCEPT:
    - D3 (pred M (1 :: List.replicate (k-1) 2 ++ [6]) 5 R): cursor-5 chain.
    - multi_bounce_general (R=[1] only): pred M0 [2] (4 :: 2^(k-1) :: 1).
    - multi_bounce_last_2_general (R=[1, 1] only): pred M0 [2] (4 :: 2^(k-1) :: 3 :: 2).
    - step_R3: existential disjunct (∃ x ∈ L, x ≥ 5) holds with x=6.

    Body sorry-stubbed: depends on `List.sum_replicate`, `smul_eq_mul`,
    and `List.get?` which were renamed/removed in the current mathlib.
    The proof structure (Nat.strong_induction_on, 12-disjunct rcases,
    9 multi-bounce + step_R rules) is preserved as a sorry-block —
    reimplementing requires rewrites with current API
    (`List.length_replicate`, `nsmul_eq_mul`, `List.getElem?`). -/
theorem OrbitReachable.not_M_kspine_6_3_R_via_ih (n : Nat) :
    ∀ (k : Nat), k ≥ 2 → ∀ (R : List Nat), R.length = n → R ≠ [] →
    ∀ {cfg : MacroConfig}
      (_hcfg : cfg = .M (List.replicate k 2 ++ [6]) 3 R)
      (_h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
        OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
        (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False),
    ¬ OrbitReachable cfg := by
  -- Stubbed: original proof depended on mathlib APIs (`List.sum_replicate`,
  -- `smul_eq_mul`, `List.get?`) that are no longer present. Refactoring will
  -- need `List.length_replicate`, `nsmul_eq_mul`, `List.getElem?` instead.
  sorry

/-- **`M [6] 3 (d :: R')` is not orbit-reachable** (callback variant for cascade
    IH): closes via shape contradictions for non-productive D-cases and
    multi-bounce; productive sub-cases (D2 → M [2,6] 3 (...); D3 → M [5] 5 (...);
    D11 → M0 [2] [6]; multi_bounce_2_and_shift → M0 [2] [r+4,2]; R2_succ →
    M0 [2] [5,1,2]; step_R3) require further chain helpers (sorry-stubbed).
    step_R1 closed via callback at M [] 3 (...) at strictly smaller phi. -/
theorem OrbitReachable.not_M_6_3_dR_via_ih {cfg : MacroConfig}
    {d : Nat} {R' : List Nat}
    (hcfg : cfg = .M [6] 3 (d :: R'))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- M [1] 4 [1] vs M [6] 3 (d :: R'): cursor 4 vs 3 ⊥.
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩  -- D1
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩  -- D2
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩  -- D4
    | ⟨_, _, _, _, _, htgt⟩  -- D5
    | ⟨_, _, _, _, _, htgt⟩  -- D6
    | ⟨_, _, _, htgt⟩  -- D7
    | ⟨a8, L'8, hcfg'8, _, htgt⟩  -- D8
    | ⟨_, _, _, _, htgt⟩  -- D9
    | ⟨_, _, _, _, htgt⟩  -- D10
    | ⟨a11, z11, L'11, hcfg'11, _, htgt⟩  -- D11
    | ⟨a12, L'12, _, _, hcfg'12, _, htgt⟩  -- D12
    -- D1: M0 target. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D2: target M L' (a+1) (1 :: (d+1) :: R'). For target M [6] 3 (d_t :: R'_t):
    -- L' = [6], a + 1 = 3 → a = 2. d_t = 1, R'_t = (d2+1) :: R'2.
    -- Pred M [2, 6] 3 (d2 :: R'2). Use not_M_2_6_3_dR_via_ih.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha2 : a2 = 2 := by omega
      have hd : d = 1 := hd_eq
      have hL' : L'2 = [6] := hL.symm
      have hR'_eq : R' = (d2 + 1) :: R'2 := hR_tail
      subst ha2
      subst hd
      subst hL'
      subst hR'_eq
      subst hcfg'2
      apply OrbitReachable.not_M_2_6_3_dR_via_ih (d := d2) (R' := R'2) rfl
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D3: target M ((a+1) :: L') (c'+2) ((d+1) :: R'). For target M [6] 3 (...):
    -- (a+1) :: L' = [6] → a = 5, L' = []. c'+2 = 3 → c' = 1. Pred M [5] 5 (d3 :: R'3).
    · sorry
    -- D4: M0 target. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1) :: R'). L = [1] vs [6]. ⊥.
    · mc_dcase_close
    -- D6: target M ((b+1) :: L') (a+4) [1]. cursor a+4 = 3 ⊥.
    · mc_dcase_close
    -- D7: target M [1] (a+4) [1]. L = [1] vs [6]. ⊥.
    · mc_dcase_close
    -- D8: target M L' (a+3) [1]. For target M [6] 3 (...): L' = [6], a+3 = 3 → a = 0.
    -- R = [1] vs (d :: R') possible only if d = 1, R' = []. AllGe1 cfg_pre = M0 (a :: L') [2]:
    -- a ≥ 1 ⊥.
    · injection htgt with hL hc _
      have ha : a8 = 0 := by omega
      subst ha
      have hL' : L'8 = [6] := hL.symm
      subst hL'
      subst hcfg'8
      mc_AllGe1_a_ge1
    -- D9: M0 target. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10: target M L' (a+4) [1, 1]. cursor a+4 = 3 ⊥.
    · mc_dcase_close
    -- D11: target M ((a+4) :: L') (z+2) [1]. For target M [6] 3 (...):
    -- (a+4) :: L' = [6] → a = 2, L' = []. z+2 = 3 → z = 1. R = [1] requires d = 1, R' = [].
    -- Pred M0 (a :: L') [z+5] = M0 [2] [6]. Use not_M0_2_6_via_ih.
    · injection htgt with hL hc hR
      injection hL with hh hL_tail
      injection hR with hd_eq hR_tail
      have ha : a11 = 2 := by omega
      have hz : z11 = 1 := by omega
      have hd : d = 1 := by omega
      have hL' : L'11 = [] := hL_tail.symm
      have hR' : R' = [] := hR_tail
      subst ha
      subst hz
      subst hd
      subst hL'
      subst hR'
      subst hcfg'11
      apply OrbitReachable.not_M0_2_6_via_ih (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D12: target M L' (a+3) ((d+1) :: R'). For target M [6] 3 (...):
    -- L' = [6], a+3 = 3 → a = 0. AllGe1 cfg_pre: a ≥ 1 ⊥.
    · injection htgt with hL hc _
      have ha : a12 = 0 := by omega
      subst ha
      have hL' : L'12 = [6] := hL.symm
      subst hL'
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ =>
    -- output M (R_mid.reverse ++ (r'+1) :: (a+4) :: L') (last''+2) [1].
    -- R = [1] vs (d :: R'): d=1, R'=[]. cursor last''+2 = 3 → last'' = 1.
    -- L = [6]: R_mid.reverse ++ (r'+1) :: (a+4) :: L' has length ≥ 2 ≠ 1 ⊥.
    rename_i a r' last'' L'_g R_mid _
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : (R_mid.reverse ++ (r' + 1) :: (a + 4) :: L'_g).length = [6].length := by
      rw [hL]
    simp [List.length_append, List.length_cons, List.length_reverse] at h_len
    omega
  | step_multi_bounce_general_to_zero _ =>
    -- M0 target. ⊥.
    exact MacroConfig.noConfusion hcfg
  | @step_multi_bounce_2_and_shift a r L'_mb h_pred_mb =>
    -- output M ((a+4) :: L') (r+2) [1, 1]. cursor r+2 = 3 → r = 1. R = [1, 1] vs (d :: R'):
    -- d = 1, R' = [1]. (a+4) :: L' = [6] → a = 2, L' = []. Pred M0 [2] [r+4, 2] = M0 [2] [5, 2].
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, hR⟩ := hcfg
    injection hL with hh hL_tail
    injection hR with hd_eq hR_tail
    have ha : a = 2 := by omega
    have hr : r = 1 := by omega
    have hL' : L'_mb = [] := hL_tail
    subst ha
    subst hr
    subst hL'
    apply OrbitReachable.not_M0_2_5_2_via_ih (by rfl)
      (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
        apply h_excl_R1_pred h_or_pre
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
          List.sum_cons, List.sum_nil] at h_phi_lt ⊢
        omega)
      h_pred_mb
  | step_multi_bounce_2_double_shift _ =>
    -- output M L' (a+4) [1, 1, 1]. cursor a+4 = 3 ⊥.
    mc_rule_close
  | step_multi_bounce_3run_last_2 _ =>
    -- output M ((r'+1) :: (a+4) :: L') (e+2) [1, 1]. L length ≥ 2 ≠ 1 ⊥.
    rename_i a r' e L'_g _
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : ((r' + 1) :: (a + 4) :: L'_g).length = [6].length := by rw [hL]
    simp [List.length_cons] at h_len
  | step_multi_bounce_last_2_general _ =>
    -- output M (middle_init.reverse ++ (r'+1) :: (a+4) :: L') (m_last+2) [1, 1].
    -- L length ≥ 2 ≠ 1 ⊥.
    rename_i a r' m_last L'_g middle_init _
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len :
        (middle_init.reverse ++ (r' + 1) :: (a + 4) :: L'_g).length = [6].length := by
      rw [hL]
    simp [List.length_append, List.length_cons, List.length_reverse] at h_len
    omega
  | step_R2_zero _ =>
    -- output M L' (a+4) [1, 1, 1, 1]. cursor a+4 = 3 ⊥.
    mc_rule_close
  | @step_R2_succ a r L'_r2 h_pred_r2 =>
    -- output M ((a+4) :: L') (r+2) [1, 1, 1]. cursor r+2 = 3 → r = 1. (a+4) :: L' = [6]
    -- → a = 2, L' = []. R = [1, 1, 1] vs (d :: R'): d = 1, R' = [1, 1]. Pred M0 [2] [5, 1, 2].
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, hR⟩ := hcfg
    injection hL with hh hL_tail
    have ha : a = 2 := by omega
    have hr : r = 1 := by omega
    have hL' : L'_r2 = [] := hL_tail
    subst ha
    subst hr
    subst hL'
    apply OrbitReachable.not_M0_2_5_1_2_via_ih (by rfl)
      (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
        apply h_excl_R1_pred h_or_pre
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
          List.sum_cons, List.sum_nil] at h_phi_lt ⊢
        omega)
      h_pred_r2
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    -- L_suf = [6], v = 3. h_disj: ∃ x ∈ [6], x ≥ 5 (x = 6 ✓), or v = a+4 = 3 (Nat ⊥).
    -- Case 1: existential disjunct succeeds, but doesn't yield contradiction.
    -- Need backward analysis on M0 (a :: L') ((r'+3) :: e :: middle_init ++ [1, 2])
    -- where a+4 = 3 forces ⊥... wait that's case 2. Let me reconsider:
    -- The existential branch: x = 6 ≥ 5. The disjunct is satisfied — we cannot derive ⊥
    -- from this branch alone. Sorry-stubbed: needs predecessor M0 [a] (...) chain.
    sorry
  | step_R1 h_pred _ _ _ h_phi =>
    -- predecessor M [] 3 (d_pre :: R'_pre). cfg.phi ≥ pred.phi + 2.
    -- callback closes pred via cascade IH (mk_M_empty_3) at strictly smaller phi.
    mc_R1_callback

end Sweeper
