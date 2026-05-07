/-
**Cascade redesign (2026-05-07)** — replaces failed Sub-plan E.3′
cu/aux mutual recursion (which was mathematically not well-founded).

**Core insight**: recurse BACKWARD on `OrbitReachable`'s `step_macro`
constructor. Backward steps DECREASE `(phi, mr)` lex by
`macroStep_lex_strict_increase`. This is the right direction for
well-founded descent.

**Predicate**: `InCascade cfg` captures cascade shapes:
  - `M [] 3 R` (the cascade target)
  - `M [2^n] 3 R` (n ≥ 1, D2-spine extension)
  - `M [1, 2^n] 5 R` (D3-lift exit)

**Stage 1** (this file): cover `mk_M_empty_3` and `mk_M_2spine_3`
cases of `cascade_strong` properly via γ.1 / γ.2. Sorry-stub the
`mk_M_1_2spine_5` case (requires γ.3 + extended cascade analysis).

See `plan-cascade-redesign.md` for the full design.
-/

import era_orbit_2adic

namespace Sweeper

open BusyLean

-- ============================================================
-- Section 1: 2-spine predicate
-- ============================================================

/-- `Is2Spine L`: every element of L is 2 (vacuous on `[]`). -/
def Is2Spine : List Nat → Prop
  | [] => True
  | x :: xs => x = 2 ∧ Is2Spine xs

@[simp] theorem Is2Spine_nil : Is2Spine [] := True.intro

@[simp] theorem Is2Spine_cons (x : Nat) (xs : List Nat) :
    Is2Spine (x :: xs) ↔ x = 2 ∧ Is2Spine xs := Iff.rfl

theorem Is2Spine_singleton_2 : Is2Spine [2] := ⟨rfl, True.intro⟩

theorem Is2Spine_cons_2 {L : List Nat} (h : Is2Spine L) :
    Is2Spine (2 :: L) := ⟨rfl, h⟩

/-- Every element of an Is2Spine list equals 2. -/
theorem Is2Spine.mem_eq_2 : ∀ {L : List Nat}, Is2Spine L → ∀ x ∈ L, x = 2
  | [], _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, ⟨h_head, h_tail⟩, x, hx =>
    match List.mem_cons.mp hx with
    | Or.inl rfl => h_head
    | Or.inr hx_tail => Is2Spine.mem_eq_2 h_tail x hx_tail

-- ============================================================
-- Section 2: InCascade inductive predicate
-- ============================================================

/-- **InCascade cfg**: cfg is a cascade shape (backward chain target
    of M [] 3 R via D2/D3). Three constructors capture:
    - `M [] 3 R` (cascade root)
    - `M [2^n] 3 R` for n ≥ 1 (D2-spine)
    - `M [1, 2^n] 5 R` for n ≥ 0 (D3-lift exit) -/
inductive InCascade : MacroConfig → Prop where
  | mk_M_empty_3 (R : List Nat) : InCascade (.M [] 3 R)
  | mk_M_2spine_3 {L : List Nat} (R : List Nat)
      (h_2s : Is2Spine L) (h_ne : L ≠ []) :
      InCascade (.M L 3 R)
  | mk_M_1_2spine_5 {L : List Nat} (R : List Nat)
      (h_2s : Is2Spine L) :
      InCascade (.M (1 :: L) 5 R)

-- ============================================================
-- Section 3: shape exclusions for non-cascade OrbitReachable cases
-- ============================================================

/-- `init = M [1] 4 [1]` is NOT in cascade (cursor 4, L head 1 ≠ 2). -/
theorem InCascade.not_init : ¬ InCascade (.M [1] 4 [1]) := by
  intro h
  cases h

/-- M [] (c+4) R is NOT in cascade for any c. -/
theorem InCascade.not_M_empty_high {c : Nat} {R : List Nat} :
    ¬ InCascade (.M [] (c + 4) R) := by
  intro h
  cases h

/-- Every element of cascade cfg's L is ≤ 2. -/
theorem InCascade.L_mem_le_2 {L : List Nat} {c : Nat} {R : List Nat}
    (h : InCascade (.M L c R)) (x : Nat) (hx : x ∈ L) : x ≤ 2 := by
  cases h with
  | mk_M_empty_3 _ => exact absurd hx List.not_mem_nil
  | mk_M_2spine_3 _ h_2s _ =>
    have := h_2s.mem_eq_2 x hx; omega
  | mk_M_1_2spine_5 _ h_2s =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := h_2s.mem_eq_2 x hx'; omega

-- ============================================================
-- Section 4: predecessor preservation under macroStep
-- ============================================================

/-- **Predecessor preservation for `mk_M_empty_3`**: if `cfg ∈ InCascade`
    via `mk_M_empty_3 R` (so `cfg = M [] 3 R`) and `macroStep cfg_pre =
    some (k, cfg)`, then `cfg_pre ∈ InCascade` via `mk_M_2spine_3 [2]`. -/
theorem InCascade.step_macro_pre_M_empty_3
    {R : List Nat} {cfg_pre : MacroConfig} {k : Nat}
    (h_inv : MacroInvariant cfg_pre)
    (h_step : macroStep cfg_pre = some (k, .M [] 3 R)) :
    InCascade cfg_pre := by
  obtain ⟨d, R', hcfg_p, _, _⟩ :=
    macroStep_M_empty_3_predecessor_form h_inv h_step
  subst hcfg_p
  exact InCascade.mk_M_2spine_3 (d :: R') ⟨rfl, True.intro⟩
    (List.cons_ne_nil _ _)

/-- **Predecessor preservation for `mk_M_2spine_3`** (length ≥ 2):
    if `cfg = M (2 :: L_out) 3 R` ∈ InCascade via `mk_M_2spine_3` and
    `macroStep cfg_pre = some (k, cfg)`, then `cfg_pre ∈ InCascade`
    via either D2 extension (`M (2 :: 2 :: L_out) 3 _`) or D3 lift
    (`M (1 :: L_out) 5 _`). -/
theorem InCascade.step_macro_pre_M_2spine_3
    {L_out : List Nat} {R : List Nat} {cfg_pre : MacroConfig} {k : Nat}
    (h_2s : Is2Spine L_out)
    (h_inv : MacroInvariant cfg_pre)
    (h_step : macroStep cfg_pre = some (k, .M (2 :: L_out) 3 R)) :
    InCascade cfg_pre := by
  rcases macroStep_M_2list_3_predecessor_form h_inv h_step with
    ⟨d, R', hcfg_p, _, _⟩ | ⟨d, R', hcfg_p, _, _⟩
  · subst hcfg_p
    exact InCascade.mk_M_2spine_3 (d :: R')
      ⟨rfl, ⟨rfl, h_2s⟩⟩ (List.cons_ne_nil _ _)
  · subst hcfg_p
    exact InCascade.mk_M_1_2spine_5 (d :: R') h_2s

-- ============================================================
-- Section 5: shape contradictions for non-step_macro constructors
-- ============================================================

-- The remaining OrbitReachable constructors (init, step_multi_bounce_*,
-- step_R2_*, step_R3, step_R1) produce specific output shapes. We
-- need to verify these don't match any InCascade shape, except where
-- step_R1's predecessor structure provides a recursion.

/-- **M0 backward exclusion**: any cfg equal to
    `M0 (1 :: 1 :: L_rest) (r :: R_rest)` with `r ≥ 2` is not
    orbit-reachable. Phrased with hcfg parameterization to sidestep
    Lean's dependent-elimination failure on `step_multi_bounce_general_to_zero`.

    The only macroStep producing this shape is D1 (sweep_to_zero),
    whose predecessor would have `L head = 0`, violating AllGe1.

    The `step_R1` sub-case requires excluding orbit-reachable
    `M [] 3 (d :: R')` predecessors with smaller phi; this is supplied
    via the `h_excl_R1_pred` callback, which the caller discharges via
    cascade IH (`ih_phi`). -/
theorem OrbitReachable.not_M0_starts_1_1_R_ge2 {cfg : MacroConfig}
    {L_rest : List Nat} {r : Nat} {R_rest : List Nat} (hr : r ≥ 2)
    (hcfg : cfg = .M0 (1 :: 1 :: L_rest) (r :: R_rest))
    (h_excl_R1_pred : ∀ {d : Nat} {R' : List Nat},
       OrbitReachable (.M [] 3 (d :: R')) →
       (MacroConfig.M [] 3 (d :: R')).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- cfg refined to M [1] 4 [1]. hcfg becomes M [1] 4 [1] = M0 (...). M ≠ M0. ⊥.
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    -- cfg refined to cfg'. h_step : macroStep cfg_pre = some (k, cfg'). hcfg : cfg' = M0 ...
    -- Substitute cfg' via hcfg in h_step.
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩
    | ⟨a, L', d, R', hcfg', _, htgt⟩
    | ⟨a, c', L', d, R', hcfg', _, htgt⟩
    | ⟨d, R', hcfg', _, htgt⟩
    | ⟨c', d, R', hcfg', _, htgt⟩
    | ⟨a, b, L', hcfg', _, htgt⟩
    | ⟨a, hcfg', _, htgt⟩
    | ⟨a, L', hcfg', _, htgt⟩
    | ⟨a, L', hcfg', _, htgt⟩
    | ⟨a, L', hcfg', _, htgt⟩
    | ⟨a, z, L', hcfg', _, htgt⟩
    | ⟨a, L', d, R', hcfg', _, htgt⟩
    -- D1: target M0 ((a+1) :: L') ((d+1) :: R'). Match.
    · injection htgt with hL hR
      injection hL with ha _
      have ha' : a = 0 := by omega
      subst ha'
      subst hcfg'
      have hinv := h_prev.macroInvariant
      have h_AllGe1 := hinv.1
      have h_a_ge1 := (AllGe1_cons.mp h_AllGe1).1
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] ((d+1) :: R'). L = [1] vs 1 :: 1 :: L_rest.
    · injection htgt with hL _
      injection hL with _ hL'
      -- hL' : 1 :: L_rest = []
      exact (List.cons_ne_nil 1 L_rest) hL'
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target M0 ((a+4) :: L') [1]. R = [1] vs r :: R_rest with r ≥ 2. ⊥.
    · injection htgt with _ hR
      injection hR with h13 _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    -- output: M (...) [1]. M ≠ M0. ⊥.
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    -- output: M0 (...) [1]. R component: [1] vs r :: R_rest with r ≥ 2.
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    -- hR : R_mid.reverse... wait hcfg is the eq cfg = M0 (1::1::L_rest) (r::R_rest)
    -- After cases refinement, cfg = M0 (...) [1]. So hcfg : M0 (...) [1] = M0 (1::1::L_rest) (r::R_rest).
    -- Injection on M0: L eq, R eq. R: [1] = r :: R_rest, so r = 1 ⊥ with r ≥ 2.
    injection hR.symm with hr_eq _
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
    -- step_R3's cfg' is M shape (from h_strict_safe's existential witness).
    -- But hcfg : cfg' = M0 (1 :: 1 :: L_rest) (r :: R_rest). M ≠ M0. ⊥.
    obtain ⟨L_suf, v, R_out, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    -- step_R1: cfg refined to step_R1 output cfg'. Predecessor is M [] 3 (d :: R').
    -- Phi side condition: cfg.phi ≥ (M [] 3 (d :: R')).phi + 2.
    -- Use the supplied callback h_excl_R1_pred at the predecessor.
    exact h_excl_R1_pred h_pred (by omega)

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
        | mk_M_1_2spine_5 R h_2s =>
          sorry  -- Stage 2: requires γ.3 + extended cascade analysis
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
      | @step_R2_succ a r L' _ =>
        -- Output: M ((a+4) :: L') (r+2) [1, 1, 1]. L head a+4.
        cases h_in with
        | @mk_M_2spine_3 L R₀ h_2s h_ne =>
          obtain ⟨h_head, _⟩ := h_2s; omega
      | @step_R3 a r' e L' middle_init _ _ h_prev _ _ _ h_safe h_strict_safe h_phi_side =>
        -- h_safe : ∀ R, cfg' ≠ M [] 3 R. Closes mk_M_empty_3 directly.
        -- h_strict_safe (2026-05-07 v2): ∃ L_suf v R_out, cfg' = M L_suf v R_out ∧
        --   ((∃ x ∈ L_suf, x ≥ 5) ∨ (v = a + 4 ∧ L_suf = L')).
        obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
        cases h_in with
        | mk_M_empty_3 R => exact h_safe R rfl
        | @mk_M_2spine_3 L R₀ h_2s h_ne =>
          -- cfg = M L 3 R₀. Inject hcfg_M to get L_suf = L, v = 3.
          rw [MacroConfig.M.injEq] at hcfg_M
          obtain ⟨hL_eq, hv_eq, _⟩ := hcfg_M
          subst hL_eq
          subst hv_eq
          rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
          · have := h_2s.mem_eq_2 x hx; omega
          · -- v = 3 = a + 4 → a = -1, impossible (a : Nat).
            omega
        | @mk_M_1_2spine_5 L_2s R₀ h_2s =>
          -- cfg = M (1 :: L_2s) 5 R₀. Inject hcfg_M.
          rw [MacroConfig.M.injEq] at hcfg_M
          obtain ⟨hL_eq, hv_eq, _⟩ := hcfg_M
          subst hL_eq
          subst hv_eq
          rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, hL_eq⟩
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
