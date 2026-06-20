/-
**#12d Case 1 chain helpers (Section 12, 2026-05-08)** —
closing the parametric Case 1 sub-sorry of `not_M_kspine_6_3_R_via_ih`'s
step_R3 (line 1184 of `era_orbit_cascade_d2.lean`).

Case 1 of step_R3's 4-case decomposition fires when:
- `mi_A.reverse ++ [e, r'+1, a+4] ++ L' = List.replicate (k'+2) 2 ++ [6]`.
- Position analysis forces `|L'| = 0`, `|mi_A| = k'`, `a = 2`, `e = 2`,
  `r' = 1`, mi_A = List.replicate k' 2 (since reverse of all-2s is same).
- Pred = `M0 [2] (4 :: 2 :: List.replicate k' 2 ++ 3 :: mi_B ++ [1, 2])`
  where `mi_B` all 1s (from inner step_R3's mi_B constraint).

**5-helper chain** (parametric in k' AND X = mi_B, all use same k'):
- L1: `M0 [2] (4 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` — D1 → L2.
- L2: `M [1] 2 (3 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` — D5 → L3.
- L3: `M [] 4 (2 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` — D12 → L4.
- L4: `M0 [1] (2 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` — D4 → L5.
- L5: `M [] 2 (1 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` — terminal.

All five helpers parametric in both `k'` and `X`. No `h_X_one` constraint
needed (closures rely on structural 1s in R).
-/

import era_orbit_cascade

namespace Sweeper

/-- **Structural decomposition for #12d Case 1.** Given the kspine equation
    `List.replicate (k'+2) 2 ++ [6] = mi_A.reverse ++ e :: (r'+1) :: (a+4) :: L'`
    and `a ≥ 1`, force `a = 2 ∧ e = 2 ∧ r' = 1 ∧ L' = [] ∧ mi_A = List.replicate k' 2`. -/
theorem case1_structure (k' : Nat) (a e r' : Nat) (L' mi_A : List Nat) (ha_ge : a ≥ 1)
    (hLsuf : List.replicate (k'+2) 2 ++ [6] = mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L') :
    a = 2 ∧ e = 2 ∧ r' = 1 ∧ L' = [] ∧ mi_A = List.replicate k' 2 := by
  -- Membership argument: every elt of LHS is 2 or 6.
  have h_LHS_mem : ∀ x ∈ (List.replicate (k'+2) 2 ++ [6]), x = 2 ∨ x = 6 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · left; exact List.eq_of_mem_replicate h
    · right; rcases List.mem_singleton.mp h with rfl; rfl
  have h_RHS_mem : ∀ x ∈ (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L'), x = 2 ∨ x = 6 := by
    intro x hx; apply h_LHS_mem; rw [hLsuf]; exact hx
  -- a+4 ∈ RHS, with a+4 ≥ 5 → a+4 = 6.
  have h_a4 : a + 4 = 2 ∨ a + 4 = 6 := h_RHS_mem _ (by
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right
    apply List.mem_cons.mpr; right
    apply List.mem_cons.mpr; left; rfl)
  have ha2 : a = 2 := by omega
  subst ha2
  -- count 6 in LHS = 1.
  have h_count_LHS : (List.replicate (k'+2) 2 ++ [6]).count 6 = 1 := by
    rw [List.count_append, List.count_replicate]; simp
  -- count 6 in RHS = 1 (via hLsuf).
  have h_count_RHS : (mi_A.reverse ++ e :: (r' + 1) :: 6 :: L').count 6 = 1 := by
    rw [← hLsuf]; exact h_count_LHS
  -- e is 2 or 6.
  have h_e : e = 2 ∨ e = 6 := h_RHS_mem _ (by
    apply List.mem_append.mpr; right; exact List.mem_cons_self)
  -- r'+1 is 2 or 6.
  have h_r1 : r' + 1 = 2 ∨ r' + 1 = 6 := h_RHS_mem _ (by
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right; exact List.mem_cons_self)
  -- e ≠ 6 and r'+1 ≠ 6 (would make count > 1).
  have h_e_ne_6 : e ≠ 6 := by
    intro h; subst h
    rw [List.count_append] at h_count_RHS
    simp [List.count_cons] at h_count_RHS
    omega
  have h_r1_ne_6 : r' + 1 ≠ 6 := by
    intro h
    rw [h] at h_count_RHS
    rw [List.count_append] at h_count_RHS
    simp [List.count_cons] at h_count_RHS
    omega
  have h_e_eq : e = 2 := by rcases h_e with h | h; exact h; exact absurd h h_e_ne_6
  subst h_e_eq
  have h_r1_eq : r' + 1 = 2 := by rcases h_r1 with h | h; exact h; exact absurd h h_r1_ne_6
  have hr : r' = 1 := by omega
  subst hr
  -- L' has no 6 and mi_A has no 6 (count argument).
  have h_count_RHS3 : (mi_A.reverse).count 6 + L'.count 6 = 0 := by
    rw [List.count_append] at h_count_RHS
    have h_simp : ((2 : ℕ) :: 2 :: 6 :: L').count 6 = 1 + L'.count 6 := by
      simp [List.count_cons]; omega
    rw [h_simp] at h_count_RHS
    omega
  have h_count_mi_A : mi_A.count 6 = 0 := by
    rw [List.count_reverse] at h_count_RHS3
    omega
  have h_count_L' : L'.count 6 = 0 := by omega
  -- All x ∈ mi_A: x ≠ 6 (count=0), so x = 2.
  have h_no6_mi_A : ∀ x ∈ mi_A, x ≠ 6 := by
    intro x hx hx6
    rw [hx6] at hx
    have := List.count_pos_iff.mpr hx
    omega
  have h_no6_L' : ∀ x ∈ L', x ≠ 6 := by
    intro x hx hx6
    rw [hx6] at hx
    have := List.count_pos_iff.mpr hx
    omega
  have h_all_mi_A_eq_2 : ∀ x ∈ mi_A, x = 2 := by
    intro x hx
    have hx_rev : x ∈ mi_A.reverse := by simp [hx]
    have h_in : x ∈ (mi_A.reverse ++ 2 :: 2 :: 6 :: L') := List.mem_append.mpr (Or.inl hx_rev)
    rcases h_RHS_mem _ h_in with h | h
    · exact h
    · exact absurd h (h_no6_mi_A _ hx)
  have h_all_L'_eq_2 : ∀ x ∈ L', x = 2 := by
    intro x hx
    have h_in : x ∈ (mi_A.reverse ++ 2 :: 2 :: 6 :: L') := by
      apply List.mem_append.mpr; right
      apply List.mem_cons.mpr; right
      apply List.mem_cons.mpr; right
      apply List.mem_cons.mpr; right; exact hx
    rcases h_RHS_mem _ h_in with h | h
    · exact h
    · exact absurd h (h_no6_L' _ hx)
  -- L' = [] via getLast argument (RHS ends with 6 if L'=[] vs ends with 2 otherwise; LHS ends with 6).
  have hL'_empty : L' = [] := by
    by_contra hL'_ne'
    have hL'_pos : L'.length ≥ 1 := by
      cases L' with
      | nil => exact absurd rfl hL'_ne'
      | cons _ _ => simp
    -- LHS.getLast = 6.
    have hLHS_last : (List.replicate (k'+2) 2 ++ [6]).getLast (by simp) = 6 := by
      rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rfl
    -- RHS.getLast = L'.getLast.
    have hRHS_ne : (mi_A.reverse ++ 2 :: 2 :: 6 :: L') ≠ [] := by
      intro h; rcases List.append_eq_nil_iff.mp h with ⟨_, h2⟩
      exact (List.cons_ne_nil _ _) h2
    have hL'_ne : L' ≠ [] := hL'_ne'
    have hRHS_last : (mi_A.reverse ++ 2 :: 2 :: 6 :: L').getLast hRHS_ne = L'.getLast hL'_ne := by
      rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rw [List.getLast_cons (List.cons_ne_nil _ _),
          List.getLast_cons (List.cons_ne_nil _ _),
          List.getLast_cons hL'_ne]
    -- L'.getLast = 2 (all L' is 2).
    have hL'_last : L'.getLast hL'_ne = 2 := h_all_L'_eq_2 _ (List.getLast_mem _)
    -- Contradiction: 6 = 2.
    have h_eq : (List.replicate (k'+2) 2 ++ [6]).getLast (by simp) =
                (mi_A.reverse ++ 2 :: 2 :: 6 :: L').getLast hRHS_ne := by
      simp [hLsuf]
    rw [hLHS_last, hRHS_last, hL'_last] at h_eq
    omega
  subst hL'_empty
  -- Now hLsuf : List.replicate (k'+2) 2 ++ [6] = mi_A.reverse ++ [2, 2, 6].
  -- Length: |mi_A| + 3 = k' + 3, so |mi_A| = k'.
  have h_len : mi_A.length = k' := by
    have h_eq : (List.replicate (k'+2) 2 ++ [6]).length =
                (mi_A.reverse ++ 2 :: 2 :: 6 :: ([] : List ℕ)).length := by rw [hLsuf]
    simp [List.length_append, List.length_cons, List.length_replicate, List.length_reverse] at h_eq
    omega
  -- mi_A is all 2s, length k', so mi_A = List.replicate k' 2.
  have hmi_eq : mi_A = List.replicate k' 2 := by
    have h_replicate : mi_A = List.replicate mi_A.length 2 :=
      (List.eq_replicate_iff.mpr ⟨rfl, h_all_mi_A_eq_2⟩)
    rw [h_replicate, h_len]
  exact ⟨rfl, rfl, rfl, rfl, hmi_eq⟩

/-- **L5 (terminal): `M [] 2 (1 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])`
    is not orbit-reachable** for all k', X. D2 closes via R[1]=1 → d=0 AllGe1 ⊥. -/
theorem OrbitReachable.not_M_empty_2_1_1_2_kspine_3_X_via_ih (k' : Nat) (X : List Nat)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 (1 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
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
    · exact MacroConfig.noConfusion htgt
    -- D2: cursor a+1=2 (a=1), L'=[]. R: 1::(d+1)::R'_pred = 1::1::2::List.replicate k' 2++3::X++[1, 2].
    --     R[1]=1 → d=0 AllGe1 ⊥.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: target L=(a+1)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D6: target.cursor=a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: target L=[1] vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D8: target.cursor=a+3 ≥ 3 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: target.cursor=a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: target L=(a+4)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: cursor 2=a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
        ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons, List.length_replicate] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_multi_bounce_last_2_general a r' m_last L' middle_init _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : (middle_init.reverse ++ (r' + 1) :: (a + 4) :: L').length =
        ([] : List Nat).length := by rw [hL]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[], v=2. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
    · exact absurd hLsuf.symm (List.cons_ne_nil _ _)
    · exact absurd hLsuf.symm (List.cons_ne_nil _ _)
    · -- a+4=2 ⊥ (a≥1 from h_prev_R3).
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L4: `M0 [1] (2 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D4 → L5. Other cases ⊥. -/
theorem OrbitReachable.not_M0_1_2_1_2_kspine_3_X_via_ih (k' : Nat) (X : List Nat)
    {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] (2 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init => exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a1, L'1, d1, R'1, hcfg'1, _, htgt⟩
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [1]=(a+1)::L' → a=0 AllGe1 ⊥.
    · injection htgt with hL _
      injection hL with ha _
      have ha0 : a1 = 0 := by omega
      subst ha0
      subst hcfg'1
      mc_AllGe1_a_ge1
    -- D2: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D3: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] ((d+1)::R'). (d+1)::R'_pred=2::1::2::List.replicate k' 2++3::X++[1, 2].
    --     d+1=2 (d=1). R'_pred=1::2::List.replicate k' 2++3::X++[1, 2].
    --     Pred = M [] 2 (1::1::2::List.replicate k' 2++3::X++[1, 2]). Use L5.
    · injection htgt with hL hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2] := hR_tail.symm
      subst hd; subst hR'
      subst hcfg'4
      apply OrbitReachable.not_M_empty_2_1_1_2_kspine_3_X_via_ih k' X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (2 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
          ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons, List.length_replicate] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (2 :: 1 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
        ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons, List.length_replicate] at h_len
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

/-- **L3: `M [] 4 (2 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D12 → L4. Other cases ⊥. -/
theorem OrbitReachable.not_M_empty_4_2_kspine_3_X_via_ih (k' : Nat) (X : List Nat)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 (2 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
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
    · exact MacroConfig.noConfusion htgt
    -- D2: target.R=1::(d+1)::R'. R[0]=1 vs 2 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: target L=(a+1)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
          ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons, List.length_replicate] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
          ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons, List.length_replicate] at h_len
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: cursor a+3=4 (a=1). target.L=[]=L'_pred. (d+1)::R'_pred=2::2::List.replicate k' 2++3::X++[1, 2].
    --     d+1=2 (d=1). R'_pred=2::List.replicate k' 2++3::X++[1, 2].
    --     Pred = M0 [1] (2::1::2::List.replicate k' 2++3::X++[1, 2]). Use L4.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hL' : L'12 = [] := hL.symm
      have hd : d12 = 1 := by omega
      have hR' : R'12 = 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_1_2_1_2_kspine_3_X_via_ih k' X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
        ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons, List.length_replicate] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_multi_bounce_last_2_general a r' m_last L' middle_init _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : (middle_init.reverse ++ (r' + 1) :: (a + 4) :: L').length =
        ([] : List Nat).length := by rw [hL]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[], v=4. Cases 1-3: empty L_suf ⊥. Case 4: a+4=4 (a=0) AllGe1 ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
    · exact absurd hLsuf.symm (List.cons_ne_nil _ _)
    · exact absurd hLsuf.symm (List.cons_ne_nil _ _)
    · have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L2: `M [1] 2 (3 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D5 → L3. Other cases ⊥. -/
theorem OrbitReachable.not_M_1_2_3_2_kspine_3_X_via_ih (k' : Nat) (X : List Nat)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 (3 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
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
    · exact MacroConfig.noConfusion htgt
    -- D2: target.R=1::(d+1)::R'. R[0]=1 vs 3 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: cursor c'+2=2 (c'=0). cfg cursor c'+4=4. (a+1)::L'_pred=[1] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[1] ✓. cursor c'+2=2 (c'=0). cfg cursor c'+4=4. (d+1)::R'_pred=3::2::List.replicate k' 2++3::X++[1, 2].
    --     d+1=3 (d=2). R'_pred=2::List.replicate k' 2++3::X++[1, 2].
    --     Pred = M [] 4 (2::2::List.replicate k' 2++3::X++[1, 2]). Use L3.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 2 := by omega
      have hR' : R'5 = 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2] := hR_tail.symm
      subst hc'; subst hd; subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_2_kspine_3_X_via_ih k' X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
          ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons, List.length_replicate] at h_len
    -- D7: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
          ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons, List.length_replicate] at h_len
    -- D8: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 (a=-2) ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cfg.L=[1]=(a+4)::L'_pred → a+4=1 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (3 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
        ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons, List.length_replicate] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1], v=2. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · injection hLsuf.symm with h_head _; omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L1 (top): `M0 [2] (4 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D1 → L2. Used to close #12d Case 1 (parametric in k' and mi_B). -/
theorem OrbitReachable.not_M0_2_4_2_kspine_3_X_via_ih (k' : Nat) (X : List Nat)
    {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] (4 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init => exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a1, L'1, d1, R'1, hcfg'1, _, htgt⟩
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [2]=(a+1)::L' → a=1, L'=[]. d+1=4 (d=3).
    --     R'=2::List.replicate k' 2++3::X++[1, 2].
    --     Pred = M [1] 2 (3::2::List.replicate k' 2++3::X++[1, 2]). Use L2.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 1 := by omega
      have hd : d1 = 3 := by omega
      have hL' : L'1 = [] := hL_eq.symm
      have hR' : R'1 = 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_1_2_3_2_kspine_3_X_via_ih k' X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [2] ⊥.
    · injection htgt with hL _
      injection hL with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (4 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
          ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons, List.length_replicate] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (4 :: 2 :: List.replicate k' 2 ++ 3 :: X ++ [1, 2]).length =
        ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons, List.length_replicate] at h_len
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

end Sweeper
