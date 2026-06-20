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

import era_orbit_macros

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
    of M [] 3 R via D2/D3). Constructors capture:
    - `M [] 3 R` (cascade root)
    - `M [2^n] 3 R` for n ≥ 1 (D2-spine)
    - `M [1, 2^n] 5 R` for n ≥ 0 (D3-lift exit)
    - `M [] 7 R` (D5/A-specific predecessor; cursor=7 fixed, narrowed
      from general `M [] (c+4) R` for tractable chain closure since
      with cursor=7 fixed many predecessor shapes are excluded by
      `phi_ge_init` directly). -/
inductive InCascade : MacroConfig → Prop where
  | mk_M_empty_3 (R : List Nat) : InCascade (.M [] 3 R)
  | mk_M_2spine_3 {L : List Nat} (R : List Nat)
      (h_2s : Is2Spine L) (h_ne : L ≠ []) :
      InCascade (.M L 3 R)
  | mk_M_1_2spine_5 {L : List Nat} (R : List Nat)
      (h_2s : Is2Spine L) :
      InCascade (.M (1 :: L) 5 R)
  | mk_M_empty_7 (R : List Nat) :
      InCascade (.M [] 7 R)

-- ============================================================
-- Section 3: shape exclusions for non-cascade OrbitReachable cases
-- ============================================================

/-- `init = M [1] 4 [1]` is NOT in cascade (cursor 4, L head 1 ≠ 2). -/
theorem InCascade.not_init : ¬ InCascade (.M [1] 4 [1]) := by
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
  | mk_M_empty_7 _ => exact absurd hx List.not_mem_nil

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
    · mc_dcase_close
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target M0 ((a+4) :: L') [1]. R = [1] vs r :: R_rest with r ≥ 2. ⊥.
    · mc_dcase_close
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
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
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

/-- **M backward exclusion (cursor 2, R=[1])**: any cfg equal to
    `M (1 :: 1 :: L_rest) 2 [1]` with `Is2Spine L_rest` is not
    orbit-reachable. Used in the backward chain from case C (D8) of
    `step_macro mk_M_1_2spine_5`.

    The Is2Spine constraint is needed for step_multi_bounce_general
    and step_R3 cases, where the output L contains an element ≥ 4 or 5
    that must lie in L_rest (since the 1's at positions 0, 1 are too
    small), contradicting `Is2Spine.mem_eq_2`. -/
theorem OrbitReachable.not_M_starts_1_1_2spine_2_R1 {cfg : MacroConfig}
    {L_rest : List Nat} (h_2s : Is2Spine L_rest)
    (hcfg : cfg = .M (1 :: 1 :: L_rest) 2 [1])
    (h_excl_R1_pred : ∀ {d : Nat} {R' : List Nat},
       OrbitReachable (.M [] 3 (d :: R')) →
       (MacroConfig.M [] 3 (d :: R')).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- cfg refined to M [1] 4 [1] vs M (1 :: 1 :: L_rest) 2 [1] — cursor mismatch.
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a, _, _, d, _, hcfg', _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1 sweep_to_zero: target M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D2 sweep_and_shift: target M L' (a+1) (1 :: (d+1) :: R'). R length ≥ 2 ≠ [1].
    · mc_dcase_close
    -- D3 sweep: target L head (a+1) = 1 → a = 0. AllGe1 of cfg_pre's L violated.
    · injection htgt with hL _ _
      injection hL with hh _
      -- hh : 1 = a + 1
      subst hcfg'
      have ha := (AllGe1_cons.mp h_prev.macroInvariant.1).1
      omega
    -- D4 sweep_to_zero_left_empty: target M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5 sweep_left_empty: target M [1] (c'+2) ((d+1) :: R'). L = [1] ≠ 1 :: 1 :: L_rest.
    · mc_dcase_close
    -- D6 era_and_sweep: target M ((b+1) :: L') (a+4) [1]. Cursor a+4 = 2 → impossible.
    · mc_dcase_close
    -- D7 era_and_sweep_solo: target M [1] (a+4) [1]. L = [1] ≠ 1 :: 1 :: L_rest.
    · mc_dcase_close
    -- D8 zero_two_solo: target M L' (a+3) [1]. Cursor a+3 = 2 → impossible (a ≥ 0).
    · mc_dcase_close
    -- D9 zero_bounce_to_zero: target M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10 zero_bounce_and_shift: target M L' (a+4) [1, 1]. R = [1, 1] ≠ [1].
    · injection htgt with _ _ hR
      injection hR with _ hR'
      -- hR' : [] = [1] (since LHS = our [1], RHS = [1, 1]; cons-injection on [1] = 1::[1] gives 1=1, []=[1])
      exact (List.cons_ne_nil _ _) hR'.symm
    -- D11 zero_bounce: target M ((a+4) :: L') (z+2) [1]. L head a+4 ≥ 4, but our L head = 1.
    · mc_dcase_close
    -- D12 zero_two: target M L' (a+3) ((d+1) :: R'). Cursor a+3 = 2 impossible.
    · mc_dcase_close
  | @step_multi_bounce_general a r' last'' L' R_mid _ =>
    -- Output: M (R_mid.reverse ++ (r'+1) :: (a+4) :: L') (last''+2) [1].
    -- (a+4) ∈ output L. By Is2Spine L_rest membership (after extracting that
    -- (a+4) ∉ {1, 1} and (a+4) ∈ L_rest), (a+4) = 2, but a+4 ≥ 4. ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_a4_in : (a + 4) ∈ R_mid.reverse ++ (r' + 1) :: (a + 4) :: L' := by
      apply List.mem_append_right
      exact List.mem_cons_of_mem _ List.mem_cons_self
    rw [hL] at h_a4_in
    rcases List.mem_cons.mp h_a4_in with h | h_tail
    · omega
    · rcases List.mem_cons.mp h_tail with h | h_in_rest
      · omega
      · have := h_2s.mem_eq_2 (a + 4) h_in_rest; omega
  | step_multi_bounce_general_to_zero _ => exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- Output R = [1, 1] ≠ [1] (length mismatch).
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
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe _ =>
    -- step_R3 strict_safe: ∃ L_suf v R_out, cfg' = M L_suf v R_out ∧ ((∃ x ∈ L_suf, x ≥ 5) ∨ (v = a+4 ∧ L_suf = L')).
    -- For cfg = M (1 :: 1 :: L_rest) 2 [1]: v = 2.
    -- v = a + 4 = 2 → a = -2 impossible. So ∃ x ∈ L_suf = 1 :: 1 :: L_rest, x ≥ 5.
    -- Elements all 1 — contradiction.
    obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
    have h_disj_2 := strict_safe_2_disjunct_of_4cases (AllGe1_cons.mp h_prev_R3.macroInvariant.1).1 h_disj
    rw [hcfg_M] at hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
    · rw [hL_eq] at hx
      rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · rcases List.mem_cons.mp hx_tail with rfl | hx_in_rest
        · omega
        · have := h_2s.mem_eq_2 x hx_in_rest; omega
    · omega  -- 2 = a + 4 impossible
  | step_R1 h_pred _ _ _ h_phi =>
    exact h_excl_R1_pred h_pred (by omega)

/-- **M0 backward exclusion (cursor 2-bounce, R=[2])**: any cfg equal
    to `M0 (2 :: 1 :: L_rest) [2]` with `Is2Spine L_rest` is not
    orbit-reachable. Used in case C (D8) of `step_macro mk_M_1_2spine_5`.

    The only productive predecessor is via D1 (sweep_to_zero) which
    gives `M (1 :: 1 :: L_rest) 2 [1]` — closed by `H1`
    (`not_M_starts_1_1_2spine_2_R1`). Other constructors produce shape
    mismatches; step_R1 closes via callback. -/
theorem OrbitReachable.not_M0_starts_2_1_2spine_2 {cfg : MacroConfig}
    {L_rest : List Nat} (h_2s : Is2Spine L_rest)
    (hcfg : cfg = .M0 (2 :: 1 :: L_rest) [2])
    (h_excl_R1_pred : ∀ {d : Nat} {R' : List Nat},
       OrbitReachable (.M [] 3 (d :: R')) →
       (MacroConfig.M [] 3 (d :: R')).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init => exact MacroConfig.noConfusion hcfg
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
    -- D1 sweep_to_zero: target M0 ((a+1) :: L') ((d+1) :: R').
    -- For target M0 (2 :: 1 :: L_rest) [2]: a + 1 = 2 (a = 1), L' = 1 :: L_rest,
    -- d + 1 = 2 (d = 1), R' = []. Predecessor: M (1 :: 1 :: L_rest) 2 [1].
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 1 := by omega
      have hd' : d = 1 := by omega
      subst ha'
      subst hd'
      have hL'' : L' = 1 :: L_rest := hL'.symm
      subst hL''
      have hR'' : R' = [] := hR'.symm
      subst hR''
      subst hcfg'
      -- Now h_prev : OrbitReachable (M (1 :: 1 :: L_rest) 2 [1]).
      apply OrbitReachable.not_M_starts_1_1_2spine_2_R1 h_2s rfl
        (h_excl_R1_pred := fun {d} {R'_pred} h_or_pred h_phi_lt => by
          refine h_excl_R1_pred h_or_pred ?_
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · injection htgt with hL _; injection hL with _ hL'; exact (List.cons_ne_nil _ _) hL'
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · injection htgt with _ hR; injection hR with hh _; omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ => exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    mc_rule_close
  | step_multi_bounce_2_and_shift _ => exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_double_shift _ => exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_3run_last_2 _ => exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_last_2_general _ => exact MacroConfig.noConfusion hcfg
  | step_R2_zero _ => exact MacroConfig.noConfusion hcfg
  | step_R2_succ _ => exact MacroConfig.noConfusion hcfg
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    exact h_excl_R1_pred h_pred (by omega)

-- ============================================================
-- Section 5b: chain-shape helpers for mk_M_empty_7 predecessor analysis
-- ============================================================

/-- **`M [3] 2 [1]` is not orbit-reachable**: phi = 6, so step_R1 contradicts
    via phi_ge_init (pred.phi ≤ 4 vs ≥ 6). Other constructors produce shape
    mismatches. -/
theorem OrbitReachable.not_M_3_2_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [3] 2 [1]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- M [1] 4 [1] vs M [3] 2 [1]: cursor mismatch (4 vs 2).
    mc_rule_close
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a, c', L', d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 target. ⊥.
    · mc_dcase_close
    -- D2: target M L' (a+1) (1 :: ...). R = [1] vs 1 :: (d+1) :: R' length ≥ 2.
    · mc_dcase_close
    -- D3 (productive): target M ((a+1) :: L') (c'+2) ((d+1) :: R').
    -- (a+1) :: L' = [3], a = 2, L' = []. c'+2 = 2, c' = 0. (d+1) :: R' = [1], d = 0 ⊥.
    · injection htgt with hL hc hR
      injection hL with hh _
      injection hR with hd_eq _
      have hd : d = 0 := by omega
      subst hd
      subst hcfg'
      have ha := (AllGe1_cons.mp h_prev.macroInvariant.2.2.1).1
      omega
    -- D4: M0 target. ⊥.
    · mc_dcase_close
    -- D5: L = [1] vs [3]. ⊥.
    · mc_dcase_close
    -- D6-D8: cursor mismatch. ⊥.
    · mc_dcase_close
    · mc_dcase_close
    · mc_dcase_close
    -- D9: M0 target. ⊥.
    · mc_dcase_close
    -- D10: cursor a+4 = 2 ⊥.
    · mc_dcase_close
    -- D11: (a+4) :: L' = [3], a + 4 = 3 ⊥.
    · mc_dcase_close
    -- D12: cursor a+3 = 2 ⊥.
    · mc_dcase_close
  | @step_multi_bounce_general a r' last'' L' R_mid _ =>
    -- output L = R_mid.reverse ++ (r'+1) :: (a+4) :: L' = [3]. (a+4) :: L' = []? cons ≠ nil ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, hc, _⟩ := hcfg
    -- hc : last''+2 = 2 → last'' = 0.
    -- hL : R_mid.reverse ++ (r'+1) :: (a+4) :: L' = [3].
    -- Length argument: LHS length ≥ 2 (R_mid.reverse + cons of cons), RHS length 1.
    have h_len : (R_mid.reverse ++ (r' + 1) :: (a + 4) :: L').length = [3].length := by
      rw [hL]
    simp [List.length_append, List.length_cons, List.length_reverse] at h_len
    omega
  | step_multi_bounce_general_to_zero _ => mc_rule_close
  | step_multi_bounce_2_and_shift _ => mc_rule_close
  | step_multi_bounce_2_double_shift _ => mc_rule_close
  | step_multi_bounce_3run_last_2 _ => mc_rule_close
  | step_multi_bounce_last_2_general _ => mc_rule_close
  | step_R2_zero _ => mc_rule_close
  | step_R2_succ _ => mc_rule_close
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [3], v = 2. h_disj: ∃ x ∈ [3], x ≥ 5 ⊥. v = a+4 = 2 ⊥ (Nat).
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

/-- **`M0 [3] [2]` is not orbit-reachable**: phi = 5 < 6, direct via
    phi_lt_six. -/
theorem OrbitReachable.not_M0_3_2 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [3] [2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  rw [hcfg] at h_or
  mc_phi_lt_six

/-- **`M [] 6 [1]` is not orbit-reachable**: chain through D8 → M0 [3] [2]
    (phi=5⊥), step_R3 phi-contradiction (pred.phi=5 < 6), step_R1
    phi-contradiction (pred.phi ≤ 5 < 6). Other constructors: shape mismatches. -/
theorem OrbitReachable.not_M_empty_6_1 {cfg : MacroConfig}
    (hcfg : cfg = .M [] 6 [1]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- M [1] 4 [1] vs M [] 6 [1]: L mismatch.
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
    | ⟨a, L', hcfg', _, htgt⟩  -- D8
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0 target. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D2: target M L' (a+1) (1 :: ...). For M [] 6 [1]: L' = [], a+1 = 6 → a = 5.
    -- R = [1] vs 1 :: (d+1) :: R' (length ≥ 2). ⊥.
    · mc_dcase_close
    -- D3: target M ((a+1) :: L') (c'+2) (...). cons L vs []. ⊥.
    · mc_dcase_close
    -- D4: M0 target. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] ... [1] vs []. ⊥.
    · mc_dcase_close
    -- D6: target M ((b+1) :: L') ... cons L vs []. ⊥.
    · mc_dcase_close
    -- D7: target M [1] ... cons vs []. ⊥.
    · mc_dcase_close
    -- D8: target M L' (a+3) [1]. For M [] 6 [1]: L' = [], a+3 = 6 → a = 3. R = [1] ✓.
    -- Pred M0 [3] [2]. Use not_M0_3_2.
    · injection htgt with hL hc _
      have ha : a = 3 := by omega
      subst ha
      have hL' : L' = [] := hL.symm
      subst hL'
      subst hcfg'
      exact OrbitReachable.not_M0_3_2 rfl h_prev
    -- D9: M0 target. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10: target M L' (a+4) [1, 1]. R = [1, 1] vs [1]. ⊥.
    · mc_dcase_close
    -- D11: target M ((a+4) :: L') ... cons L vs []. ⊥.
    · mc_dcase_close
    -- D12: target M L' (a+3) ((d+1) :: R'). R = (d+1) :: R' = [1]. d+1 = 1, d = 0 violates AllGe1.
    · rename_i d _ hcfg'_pre _
      injection htgt with hL hc hR
      injection hR with hd_eq _
      have hd : d = 0 := by omega
      subst hd
      subst hcfg'_pre
      -- cfg_pre = M0 (? :: ?) (2 :: 0 :: R'). AllGe1 R = AllGe1 (2 :: 0 :: R'). Tail head 0 violates.
      have hAR := h_prev.macroInvariant.2.1
      have h2 := (AllGe1_cons.mp hAR).2
      have ha := (AllGe1_cons.mp h2).1
      omega
  | step_multi_bounce_general _ =>
    -- output L = R_mid.reverse ++ ... :: ... :: L' = []. Cons ≠ nil. ⊥.
    rename_i a r' last'' L' R_mid _
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : (R_mid.reverse ++ (r' + 1) :: (a + 4) :: L').length =
        ([] : List Nat).length := by
      exact congr_arg List.length hL
    simp [List.length_append, List.length_cons, List.length_reverse] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- output M ((a+4) :: L') (r+2) [1, 1]. cons L vs []. ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    -- R [1, 1, 1] vs [1] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with _ hR_tail
    exact (List.cons_ne_nil _ _) hR_tail
  | step_multi_bounce_3run_last_2 _ =>
    -- cons L vs []. ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_last_2_general _ =>
    -- output L = middle_init.reverse ++ ... :: ... :: L'. Cons ≠ []. ⊥.
    rename_i a r' m_last L' middle_init _
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : (middle_init.reverse ++ (r' + 1) :: (a + 4) :: L').length =
        ([] : List Nat).length := by
      exact congr_arg List.length hL
    simp [List.length_append, List.length_cons, List.length_reverse] at h_len
  | step_R2_zero _ =>
    -- R [1, 1, 1, 1] vs [1] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with _ hR_tail
    exact (List.cons_ne_nil _ _) hR_tail
  | step_R2_succ _ =>
    -- cons L vs []. ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- cfg' = M L_suf v R_out. h_disj: ∃ x ∈ L_suf, x ≥ 5 ⊥ (L_suf = []) OR
    -- v = a+4 = 6, a = 2, L_suf = L' = [].
    -- Pred M0 (a :: L') (...) = M0 [2] (...). h_phi_side: cfg.phi = pred.phi + 2.
    -- pred.phi = 7 - 2 = 5 < 6 ⊥ via phi_lt_six.
    obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
    have h_disj_2 := strict_safe_2_disjunct_of_4cases (AllGe1_cons.mp h_prev_R3.macroInvariant.1).1 h_disj
    rw [hcfg_M] at hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, hR_eq⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, _⟩ | ⟨h_v_eq, hL_eq⟩
    · exact absurd hx List.not_mem_nil
    · have ha : a = 2 := by omega
      subst ha
      have hL'' : L' = [] := hL_eq.symm
      subst hL''
      have hR_out : R_out = [1] := hR_eq
      subst hR_out
      -- hcfg_M : cfg' = M [] 6 [1]. subst to propagate to h_phi_side.
      subst hcfg_M
      -- h_phi_side : (M [] 6 [1]).phi = (M0 [2] ((r'+3) :: e :: middle_init ++ [1, 2])).phi + 2.
      -- = 7 = r' + e + middle_init.sum + 10 → ⊥.
      simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
        List.sum_append, List.sum_cons, List.sum_nil] at h_phi_side
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    -- cfg.phi = 7. pred.phi ≤ 5 < 6. ⊥.
    have h_pred_phi := h_pred.phi_ge_init
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi h_pred_phi
    omega

/-- **`M [1] 4 [2]` is not orbit-reachable**: chain through D5 → M [] 6 [1].
    Other rules: shape mismatches; step_R1 phi-contradiction (cfg.phi = 7). -/
theorem OrbitReachable.not_M_1_4_2 {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 4 [2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- M [1] 4 [1] vs M [1] 4 [2]: R mismatch.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, hcfg'_D3, _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩
    | ⟨c', d, R', hcfg'_D5, _, htgt⟩  -- D5
    | ⟨_, _, _, hcfg'_D6, _, htgt⟩  -- D6
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩  -- D12
    -- D1: M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D2: target M L' (a+1) (1 :: (d+1) :: R'). For target M [1] 4 [2]:
    -- R = [2] vs 1 :: (d+1) :: R'. head 2 vs 1 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: target M ((a+1) :: L') ... For [1] 4 [2]: (a+1) :: L' = [1], a = 0 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      subst hcfg'_D3
      have ha := (AllGe1_cons.mp h_prev.macroInvariant.1).1
      omega
    -- D4: M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1) :: R'). For [1] 4 [2]: c'+2 = 4 → c' = 2.
    -- R = [2] = (d+1) :: R'. d = 1, R' = []. Pred M [] 6 [1]. Use not_M_empty_6_1.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c' = 2 := by omega
      have hd' : d = 1 := by omega
      subst hc'
      subst hd'
      have hR'' : R' = [] := hR_tail.symm
      subst hR''
      subst hcfg'_D5
      exact OrbitReachable.not_M_empty_6_1 rfl h_prev
    -- D6: target M ((b+1) :: L') (a+4) [1]. R = [1] vs [2] ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D7: target M [1] (a+4) [1]. R = [1] vs [2] ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D8: target M L' (a+3) [1]. R = [1] vs [2] ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D9: M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10: target M L' (a+4) [1, 1]. R = [1, 1] vs [2]. ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D11: target M ((a+4) :: L') (z+2) [1]. (a+4) :: L' = [1], a + 4 = 1 ⊥.
    · mc_dcase_close
    -- D12: target M L' (a+3) ((d+1) :: R'). cursor a+3 = 4, a = 1. L' = [1].
    -- R = (d+1) :: R' = [2]. d = 1, R' = []. Pred M0 [1, 1] [2, 1]. phi = 5 < 6 ⊥.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hd : d12 = 1 := by omega
      have hL' : L'12 = [1] := hL.symm
      have hR' : R'12 = [] := hR_tail.symm
      subst ha
      subst hd
      subst hL'
      subst hR'
      subst hcfg'12
      refine OrbitReachable.not_phi_lt_six ?_ h_prev
      simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
      omega
  | step_multi_bounce_general _ =>
    -- output cursor last''+2 = 4, last'' = 2. R = [1] vs [2]. ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- R [1, 1] vs [2] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    -- R [1, 1, 1] vs [2] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_3run_last_2 _ =>
    -- R [1, 1] vs [2] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_last_2_general _ =>
    -- R [1, 1] vs [2] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_zero _ =>
    -- R [1, 1, 1, 1] vs [2] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    -- R [1, 1, 1] vs [2] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf = [1], v = 4. h_disj: ∃ x ∈ [1] x ≥ 5 (1 < 5) ⊥. v = a+4 = 4, a = 0 violates AllGe1.
    obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
    have h_disj_2 := strict_safe_2_disjunct_of_4cases (AllGe1_cons.mp h_prev_R3.macroInvariant.1).1 h_disj
    rw [hcfg_M] at hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj_2 with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, hL_eq⟩
    · rcases List.mem_cons.mp hx with rfl | hx_tail
      · omega
      · exact absurd hx_tail List.not_mem_nil
    · -- v = a+4 = 4, a = 0. h_prev_R3 : OrbitReachable (M0 (0 :: L') (...)).
      -- AllGe1 of (0 :: L') gives 0 ≥ 1 ⊥.
      have ha_ge1 := (AllGe1_cons.mp h_prev_R3.macroInvariant.1).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    have h_pred_phi := h_pred.phi_ge_init
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi h_pred_phi
    omega

/-- **`M [2] 2 [3]` is not orbit-reachable**: chain through D3 → M [1] 4 [2].
    Other rules: shape mismatches; step_R1 phi-contradiction (cfg.phi = 7). -/
theorem OrbitReachable.not_M_2_2_3 {cfg : MacroConfig}
    (hcfg : cfg = .M [2] 2 [3]) :
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
    | ⟨a, c', L', d, R', hcfg', _, htgt⟩  -- D3
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D2: target M L' (a+1) (1 :: ...). cursor 2 = a+1, a = 1. R = [3] vs 1 :: ... head 1 vs 3 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: target M ((a+1) :: L') (c'+2) ((d+1) :: R'). For M [2] 2 [3]:
    -- (a+1) :: L' = [2], a = 1, L' = []. c'+2 = 2, c' = 0. (d+1) :: R' = [3], d = 2, R' = [].
    -- Pred M [1] 4 [2]. Use not_M_1_4_2.
    · injection htgt with hL hc hR
      injection hL with hh hL_tail
      injection hR with hd_eq hR_tail
      have ha : a = 1 := by omega
      have hc' : c' = 0 := by omega
      have hd : d = 2 := by omega
      have hL' : L' = [] := hL_tail.symm
      have hR' : R' = [] := hR_tail.symm
      subst ha
      subst hc'
      subst hd
      subst hL'
      subst hR'
      subst hcfg'
      exact OrbitReachable.not_M_1_4_2 rfl h_prev
    -- D4: M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1) :: R'). L = [1] vs [2] ⊥.
    · mc_dcase_close
    -- D6: cursor a+4 = 2 ⊥.
    · mc_dcase_close
    -- D7: cursor a+4 = 2 ⊥.
    · mc_dcase_close
    -- D8: cursor a+3 = 2 ⊥.
    · mc_dcase_close
    -- D9: M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4 = 2 ⊥.
    · mc_dcase_close
    -- D11: (a+4) :: L' = [2], a+4 = 2 ⊥.
    · mc_dcase_close
    -- D12: cursor a+3 = 2 ⊥.
    · mc_dcase_close
  | step_multi_bounce_general _ =>
    -- output cursor last''+2 = 2, last'' = 0. R = [1] vs [3] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- output L = (a+4) :: L' vs [2]. a+4 = 2 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    -- R [1, 1, 1] vs [3] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_3run_last_2 _ =>
    -- output L (r'+1) :: (a+4) :: L' vs [2]. (a+4) :: L' = [] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with _ hL_tail
    exact (List.cons_ne_nil _ _) hL_tail
  | step_multi_bounce_last_2_general _ =>
    -- output L middle_init.reverse ++ (r'+1) :: (a+4) :: L'. R = [1, 1] vs [3] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_zero _ =>
    -- R [1, 1, 1, 1] vs [3] ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    -- output L (a+4) :: L' vs [2]. ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_R3 h_prev_R3 _ _ _ _ h_strict_safe _ =>
    -- L_suf = [2], v = 2. h_disj: ∃ x ∈ [2], x ≥ 5 (2 < 5) ⊥. v = a+4 = 2 ⊥.
    obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
    have h_disj_2 := strict_safe_2_disjunct_of_4cases (AllGe1_cons.mp h_prev_R3.macroInvariant.1).1 h_disj
    rw [hcfg_M] at hcfg
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
    have h_pred_phi := h_pred.phi_ge_init
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi h_pred_phi
    omega

/-- **`M0 [3] [4]` is not orbit-reachable**: D1 backward predecessor is
    `M [2] 2 [3]` (excluded). Other constructors fail by shape; step_R1
    phi-contradiction. -/
theorem OrbitReachable.not_M0_3_4 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [3] [4]) :
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
    | ⟨d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: target M0 ((a+1) :: L') ((d+1) :: R'). For M0 [3] [4]: a = 2, d = 3, L' = R' = [].
    -- Pred M [2] 2 [3]. Use not_M_2_2_3.
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 2 := by omega
      have hd' : d = 3 := by omega
      have hL'' : L' = [] := hL'.symm
      have hR'' : R' = [] := hR'.symm
      subst ha'
      subst hd'
      subst hL''
      subst hR''
      subst hcfg'
      exact OrbitReachable.not_M_2_2_3 rfl h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] ((d+1) :: R'). [1] = [3] ⊥.
    · injection htgt with hL _
      injection hL with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target M0 ((a+4) :: L') [1]. R = [1] vs [4] ⊥.
    · injection htgt with _ hR
      injection hR with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    -- output M0 (...) [1]. R = [1] vs [4] ⊥.
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
    -- M target ≠ M0. ⊥.
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    have h_pred_phi := h_pred.phi_ge_init
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
      List.sum_cons, List.sum_nil] at h_phi h_pred_phi
    omega

/-- **`M0 [4] [2]` is not orbit-reachable**: only D1 backward predecessor is
    `M [3] 2 [1]`, which is not reachable (`not_M_3_2_1`). Other constructors
    fail by shape mismatch; step_R1 fails via phi-contradiction
    (cfg.phi = 6 vs predecessor.phi ≥ 6). -/
theorem OrbitReachable.not_M0_4_2 {cfg : MacroConfig}
    (hcfg : cfg = .M0 [4] [2]) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- M ≠ M0. ⊥.
    exact MacroConfig.noConfusion hcfg
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨a, L', d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, _, htgt⟩
    | ⟨d, R', hcfg', _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    -- D1: target M0 ((a+1) :: L') ((d+1) :: R'). For target M0 [4] [2]:
    -- a+1 = 4 (a = 3), L' = []. d+1 = 2 (d = 1), R' = []. Pred M [3] 2 [1].
    · injection htgt with hL hR
      injection hL with ha hL'
      injection hR with hd hR'
      have ha' : a = 3 := by omega
      have hd' : d = 1 := by omega
      subst ha'
      subst hd'
      have hL'' : L' = [] := hL'.symm
      subst hL''
      have hR'' : R' = [] := hR'.symm
      subst hR''
      subst hcfg'
      exact OrbitReachable.not_M_3_2_1 rfl h_prev
    -- D2: target M (...). M ≠ M0. ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D3: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] ((d+1) :: R'). [1] = [4] ⊥ (1 ≠ 4).
    · injection htgt with hL _
      injection hL with hh _
      omega
    -- D5: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D6: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D7: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D8: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D9: target M0 ((a+4) :: L') [1]. R = [1] vs [2]. ⊥.
    · injection htgt with _ hR
      injection hR with hh _
      omega
    -- D10: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D11: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D12: target M (...). ⊥.
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    -- target M (...). ⊥.
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    -- target M0 (...) [1]. R = [1] vs [2]. ⊥.
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
    -- cfg' = M L_suf v R_out. M target ≠ M0 [4] [2]. ⊥.
    obtain ⟨_, _, _, hcfg_M, _⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
    exact MacroConfig.noConfusion hcfg
  | step_R1 h_pred _ _ _ h_phi =>
    -- cfg.phi = 6. h_phi: pred.phi + 2 ≤ 6 → pred.phi ≤ 4. phi_ge_init: pred.phi ≥ 6. ⊥.
    have h_pred_phi := h_pred.phi_ge_init
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
      List.sum_cons, List.sum_nil] at h_phi h_pred_phi
    omega

-- ============================================================
-- Section 8: Chain helpers for #20 (mk_M_empty_7 step_R3 closure)
-- ============================================================
-- Chain: M0 [3] (3 :: 1 :: X ++ [1, 2]) ← D1 ← M [2] 2 (2 :: 1 :: X ++ [1, 2])
--         ← D3 ← M [1] 4 (1 :: 1 :: X ++ [1, 2]). Each level all-closes via
-- shape ⊥ / AllGe1 ⊥ / step_R3 4-case ⊥ / step_R1 callback. Parametric in X.

/-- **`M [1] 4 (1 :: 1 :: X ++ [1, 2])` is not orbit-reachable** (callback variant).
    All forward producers close. -/
theorem OrbitReachable.not_M_1_4_for_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 4 (1 :: 1 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    -- hcfg : M [1] 4 [1] = M [1] 4 (1::1::X++[1, 2]).
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : ([1] : List Nat).length = (1 :: 1 :: X ++ [1, 2]).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨c'5, d5, R'5, hcfg'5, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    -- D1: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D2: target M L'2 (a+1) (1::(d+1)::R'2). cursor 4 = a+1 (a=3). L'2=[1].
    --     R = 1::(d+1)::R'_2. R[1] = (d+1) = 1 → d=0. AllGe1 ⊥.
    · injection htgt with hL hc hR
      have ha : a2 = 3 := by omega
      injection hR with hd_eq hR_tail
      injection hR_tail with hd_eq2 _
      have hd : d2 = 0 := by omega
      subst ha; subst hd
      subst hcfg'2
      have hAL := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAL).1
      omega
    -- D3: (a+1)::L'3 = [1] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1)::R'). c'+2 = 4 → c'=2. (d+1)::R' = R = 1::1::X++[1, 2].
    --     d+1 = 1 → d=0. AllGe1 ⊥.
    · injection htgt with _ hc hR
      injection hR with hd_eq _
      have hd : d5 = 0 := by omega
      subst hd
      subst hcfg'5
      have hAL := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAL).1
      omega
    -- D6: target R=[1]. R has length ≥ 4 mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: same.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D8: target R=[1]. Mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1]. Mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target R=[1]. Mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D12: cursor 4 = a+3 (a=1). L'12=[1]. (d+1)::R' = R[0]=1 → d=0 AllGe1 ⊥.
    --     pred M0 form: macroInvariant.2.1 = AllGe1 R, R = 2::d::R'12 = 2::0::...
    · injection htgt with hL hc hR
      have ha : a12 = 1 := by omega
      injection hR with hd_eq _
      have hd : d12 = 0 := by omega
      subst ha; subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have h_tail := (AllGe1_cons.mp hAR).2
      have hd_ge := (AllGe1_cons.mp h_tail).1
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_last_2_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    -- hR : [1, 1, 1, 1] = 1 :: 1 :: X ++ [1, 2]. Inject deeply, X = [] forced; element ⊥.
    injection hR with _ hR1
    injection hR1 with _ hR2
    -- hR2 : [1, 1] = X ++ [1, 2]
    cases X with
    | nil => injection hR2 with _ hR3; injection hR3 with hh _; omega
    | cons xh xt =>
      have h_len : ([1, 1] : List Nat).length = ((xh :: xt) ++ [1, 2]).length := by
        rw [hR2]; rfl
      simp [List.length_append, List.length_cons] at h_len
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf = [1], v = 4. 4-case all ⊥.
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
    · -- a+4 = 4 → a = 0, AllGe1 ⊥.
      have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M [2] 2 (2 :: 1 :: X ++ [1, 2])` is not orbit-reachable** (callback variant).
    D3 productive → `not_M_1_4_for_X_via_ih`. Other cases close via shape ⊥. -/
theorem OrbitReachable.not_M_2_2_for_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [2] 2 (2 :: 1 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: cursor 2 = a+1 (a=1). R[0] = 2 ≠ 1 ⊥.
    · injection htgt with _ _ hR
      injection hR with hd _
      omega
    -- D3: pred M [1] 4 (1::1::X++[1, 2]). Use level 1.
    · injection htgt with hL hc hR
      injection hL with ha_eq hL_rest
      injection hR with hd_eq hR_tail
      have ha : a3 = 1 := by omega
      have hc : c'3 = 0 := by omega
      have hL' : L'3 = [] := hL_rest.symm
      have hd : d3 = 1 := by omega
      have hR' : R'3 = 1 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hc; subst hL'; subst hd; subst hR'
      subst hcfg'3
      apply OrbitReachable.not_M_1_4_for_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D4: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs [2] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D6: R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target L=[1] vs [2] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D8: R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D9: M0 ⊥
    · exact MacroConfig.noConfusion htgt
    -- D10: R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D12: cursor 2 = a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_last_2_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    -- hR : [1, 1, 1, 1] = 2 :: 1 :: X ++ [1, 2]. Head: 1 = 2 ⊥.
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[2], v=2. 4-case all ⊥.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([2] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([2] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · injection hLsuf.symm with h_head _; omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **`M0 [3] (3 :: 1 :: X ++ [1, 2])` is not orbit-reachable** (callback variant).
    D1 productive → `not_M_2_2_for_X_via_ih`. Other cases close via shape ⊥. -/
theorem OrbitReachable.not_M0_3_for_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [3] (3 :: 1 :: X ++ [1, 2]))
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
      ⟨a, L', d, R', hcfg'1, _, htgt⟩
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
    -- D1: pred M [2] 2 (2::1::X++[1, 2]). Use level 2.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a = 2 := by omega
      have hd : d = 2 := by omega
      have hL' : L' = [] := hL_eq.symm
      have hR' : R' = 1 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_2_2_for_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D2: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D3: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [3] ⊥.
    · injection htgt with hL _
      injection hL with hh _
      omega
    -- D5: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D6: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D7: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D8: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (3 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D10: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D11: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D12: M ⊥
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (3 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
-- Section 9: Chain helpers for #14 Case 3 (M [6] 3 (d::R') step_R3)
-- ============================================================
-- 6-level chain for pred = M0 [2] (5 :: 1 :: X ++ [1, 2]):
--   M0 [2] (5::1::X++[1, 2]) ← D1 ← M [1] 2 (4::1::X++[1, 2])
--   ← D5 ← M [] 4 (3::1::X++[1, 2]) ← D12 ← M0 [1] (2::2::1::X++[1, 2])
--   ← D4 ← M [] 2 (1::2::1::X++[1, 2]) ← D2 ← M [1] 3 (1::1::X++[1, 2]).
-- Level 6 closes all backward via AllGe1 ⊥ / step_R3 4-case / step_R1.

/-- **Level 6: `M [1] 3 (1 :: 1 :: X ++ [1, 2])` is not orbit-reachable**. -/
theorem OrbitReachable.not_M_1_3_X_terminal_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 3 (1 :: 1 :: X ++ [1, 2]))
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
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
    -- D2: cursor 3 = a+1 (a=2), L'=[1]. R = 1::(d+1)::R'. R[0]=1 ✓, (d+1)=R[1]=1 → d=0 AllGe1.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: (a+1)::L'=[1] → a=0 AllGe1.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] ✓. cursor 3 = c'+2 → c'=1, cfg cursor 5. (d+1)::R'=R[0]=1 → d=0 AllGe1.
    · injection htgt with _ hc hR
      injection hR with hd_eq _
      have hd : d5 = 0 := by omega
      subst hd
      subst hcfg'5
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D12: cursor 3 = a+3 (a=0) AllGe1 ⊥.
    · rename_i a12 L'12 d12 R'12 hcfg'12 _
      injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_last_2_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    -- target M L' (a+4) [1, 1, 1, 1]. cursor a+4 ≥ 4 ≠ 3.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1], v=3. 4-case all ⊥.
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

/-- **Level 5: `M [] 2 (1 :: 2 :: 1 :: X ++ [1, 2])` is not orbit-reachable**.
    D2 productive → level 6. Other cases ⊥. -/
theorem OrbitReachable.not_M_empty_2_1_2_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 (1 :: 2 :: 1 :: X ++ [1, 2]))
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
    -- D2: target M L'2 (a+1) (1::(d+1)::R'). cursor 2 = a+1 (a=1). L'2=[].
    --     R = 1::(d+1)::R'_pred = 1::2::1::X++[1, 2]. d+1=2 (d=1). R'_pred = 1::X++[1, 2].
    --     Pred M [1] 3 (1::1::X++[1, 2]). Use level 6.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR_tail2
      have ha : a2 = 1 := by omega
      have hL' : L'2 = [] := hL.symm
      have hd : d2 = 1 := by omega
      have hR' : R'2 = 1 :: X ++ [1, 2] := hR_tail2.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'2
      apply OrbitReachable.not_M_1_3_X_terminal_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D3: target L=(a+1)::L' vs []. ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D4: target M0 [1] (...). M0 ⊥ for M cfg.
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs []. ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D6: R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target L=[1] vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 2 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target L=(a+4)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: cursor 2 = a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    -- target L = middle_init.reverse ++ (r'+1)::(a+4)::L'. For target L=[], length 0 vs ≥ 2.
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
    -- L_suf=[], v=2. 4-case all ⊥.
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
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **Level 4: `M0 [1] (2 :: 2 :: 1 :: X ++ [1, 2])` is not orbit-reachable**.
    D4 productive → level 5. Other cases ⊥. -/
theorem OrbitReachable.not_M0_1_2_2_1_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] (2 :: 2 :: 1 :: X ++ [1, 2]))
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
    -- D1: (a+1)::L' = [1] → a=0 AllGe1 ⊥.
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
    -- D4: target M0 [1] ((d+1)::R'). cfg from M [] 2 (d::R'). target R = (d+1)::R' = 2::2::1::X++[1, 2].
    --     d+1=2 (d=1). R'=2::1::X++[1, 2]. Pred M [] 2 (1::2::1::X++[1, 2]). Use level 5.
    · injection htgt with hL hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = 2 :: 1 :: X ++ [1, 2] := hR_tail.symm
      subst hd; subst hR'
      subst hcfg'4
      apply OrbitReachable.not_M_empty_2_1_2_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D5: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D6: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D7: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D8: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (2 :: 2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D10: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D11: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D12: M ⊥
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (2 :: 2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **Level 3: `M [] 4 (3 :: 1 :: X ++ [1, 2])` is not orbit-reachable**.
    D12 productive → level 4. Other cases ⊥. -/
theorem OrbitReachable.not_M_empty_4_3_1_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 (3 :: 1 :: X ++ [1, 2]))
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
    -- D2: target M L' (a+1) (1::(d+1)::R'). target = M [] 4 (3::1::X++[1, 2]).
    --     L'=[], a+1=4 (a=3). 1::(d+1)::R'_pred = 3::1::X++[1, 2]. 1=3 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs []. ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · injection htgt with _ _ hR
      have h_len : (3 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: target M L' (a+3) ((d+1)::R'). For target M [] 4 (3::1::X++[1, 2]):
    --     L'=[], a+3=4 (a=1). (d+1)::R' = 3::1::X++[1, 2]. d+1=3 (d=2). R' = 1::X++[1, 2].
    --     Pred M0 [1] (2::2::1::X++[1, 2]). Use level 4.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hL' : L'12 = [] := hL.symm
      have hd : d12 = 2 := by omega
      have hR' : R'12 = 1 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_1_2_2_1_X_via_ih X (by rfl)
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
    have h_len : (3 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (3 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    -- target R=[1, 1, 1, 1] vs 3::1::X++[1, 2]. R[0]=3≠1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[], v=4. 4-case all ⊥.
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
    · -- a+4 = 4 → a = 0 AllGe1 ⊥.
      have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **Level 2: `M [1] 2 (4 :: 1 :: X ++ [1, 2])` is not orbit-reachable**.
    D5 productive → level 3. Other cases ⊥. -/
theorem OrbitReachable.not_M_1_2_4_1_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 (4 :: 1 :: X ++ [1, 2]))
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
    -- D2: cursor 2 = a+1 (a=1). R[0]=4≠1 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: (a+1)::L'=[1] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1)::R'). cursor 2 = c'+2 (c'=0). cfg cursor 4.
    --     (d+1)::R' = R = 4::1::X++[1, 2]. d+1=4 (d=3). R'=1::X++[1, 2].
    --     Pred M [] 4 (3::1::X++[1, 2]). Use level 3.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 3 := by omega
      have hR' : R'5 = 1 :: X ++ [1, 2] := hR_tail.symm
      subst hc'; subst hd; subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_3_1_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6: R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target L=[1]. Match cfg [1]. R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D8: cursor 2 = a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D12: cursor 2 = a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_last_2_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: 1 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1], v=2. 4-case all ⊥.
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

/-- **Level 1: `M0 [2] (5 :: 1 :: X ++ [1, 2])` is not orbit-reachable**.
    D1 productive → level 2. Other cases ⊥. Used to close #14 Case 3. -/
theorem OrbitReachable.not_M0_2_5_1_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] (5 :: 1 :: X ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). For target M0 [2] (5::1::X++[1, 2]):
    --     (a+1)::L' = [2] → a=1, L'=[]. (d+1)::R' = 5::1::X++[1, 2]. d+1=5 (d=4). R'=1::X++[1, 2].
    --     Pred M [1] 2 (4::1::X++[1, 2]). Use level 2.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 1 := by omega
      have hd : d1 = 4 := by omega
      have hL' : L'1 = [] := hL_eq.symm
      have hR' : R'1 = 1 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_1_2_4_1_X_via_ih X (by rfl)
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
      have h_len : (5 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (5 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
-- Section 10: Chain helpers for #4 Case 2 (M [2, 6] 3 (d::R') step_R3)
-- ============================================================
-- 5-level chain for pred = M0 [2] (4 :: 3 :: X ++ [1, 2]):
--   M0 [2] (4::3::X++[1, 2]) ← D1 ← M [1] 2 (3::3::X++[1, 2])
--   ← D5 ← M [] 4 (2::3::X++[1, 2]) ← D12 ← M0 [1] (2::1::3::X++[1, 2])
--   ← D4 ← M [] 2 (1::1::3::X++[1, 2]).
-- Level 5 closes all backward via AllGe1 ⊥ / step_R3 4-case / step_R1.

/-- **Level 5: `M [] 2 (1 :: 1 :: 3 :: X ++ [1, 2])` is not orbit-reachable**.
    All backward cases close via shape ⊥ / AllGe1 ⊥ / step_R3 4-case / step_R1. -/
theorem OrbitReachable.not_M_empty_2_1_1_3_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [] 2 (1 :: 1 :: 3 :: X ++ [1, 2]))
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
    -- D2: target M L' (a+1) (1::(d+1)::R'). cursor 2=a+1 (a=1), L'=[]. R = 1::(d+1)::R'_pred =
    --     1::1::3::X++[1, 2]. d+1=1 (d=0). R'_pred = 3::X++[1, 2]. AllGe1 ⊥ on d=0.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: target L=(a+1)::L' vs []. ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D4: target M0 ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs []. ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D6: target cursor=a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: target cursor=a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D8: target cursor=a+3 ≥ 3 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D9: target M0 ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10: target cursor=a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: target L=(a+4)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: cursor 2 = a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    -- L_suf=[], v=2. 4-case all ⊥.
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
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **Level 4: `M0 [1] (2 :: 1 :: 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D4 productive → Level 5. Other cases ⊥. -/
theorem OrbitReachable.not_M0_1_2_1_3_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1] (2 :: 1 :: 3 :: X ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [1] vs (a+1)::L' → a=0 AllGe1 ⊥.
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
    -- D4: target M0 [1] ((d+1)::R'). For target M0 [1] (2::1::3::X++[1, 2]):
    --     d+1=2 (d=1). R'=1::3::X++[1, 2]. Pred M [] 2 (1::1::3::X++[1, 2]). Use Level 5.
    · injection htgt with hL hR
      injection hR with hd_eq hR_tail
      have hd : d4 = 1 := by omega
      have hR' : R'4 = 1 :: 3 :: X ++ [1, 2] := hR_tail.symm
      subst hd; subst hR'
      subst hcfg'4
      apply OrbitReachable.not_M_empty_2_1_1_3_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D5: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D6: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D7: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D8: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (2 :: 1 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D10: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D11: M ⊥
    · exact MacroConfig.noConfusion htgt
    -- D12: M ⊥
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (2 :: 1 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **Level 3: `M [] 4 (2 :: 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D12 productive → Level 4. Other cases ⊥. -/
theorem OrbitReachable.not_M_empty_4_2_3_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 (2 :: 3 :: X ++ [1, 2]))
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
    -- D2: target M L' (a+1) (1::(d+1)::R'). For target M [] 4 (2::3::X++[1, 2]):
    --     L'=[], a+1=4 (a=3). 1::(d+1)::R'_pred = 2::3::X++[1, 2]. 1=2 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: target L=(a+1)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D4: target M0 ⊥.
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
      have h_len : (2 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · injection htgt with _ _ hR
      have h_len : (2 :: 3 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: target M L' (a+3) ((d+1)::R'). For target M [] 4 (2::3::X++[1, 2]):
    --     L'=[], a+3=4 (a=1). (d+1)::R'_pred = 2::3::X++[1, 2]. d+1=2 (d=1). R'_pred = 3::X++[1, 2].
    --     Pred M0 [1] (2::1::3::X++[1, 2]). Use Level 4.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 1 := by omega
      have hL' : L'12 = [] := hL.symm
      have hd : d12 = 1 := by omega
      have hR' : R'12 = 3 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_1_2_1_3_X_via_ih X (by rfl)
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
    have h_len : (2 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 3 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    -- L_suf=[], v=4. 4-case all ⊥.
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
    · -- a+4 = 4 → a = 0 AllGe1 ⊥.
      have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **Level 2: `M [1] 2 (3 :: 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D5 productive → Level 3. Other cases ⊥. -/
theorem OrbitReachable.not_M_1_2_3_3_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 (3 :: 3 :: X ++ [1, 2]))
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
    -- D2: target M L' (a+1) (1::(d+1)::R'). cursor 2=a+1 (a=1). R[0]=1 vs 3 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: target L=(a+1)::L' = [1] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    -- D4: target M0 ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D5: target M [1] (c'+2) ((d+1)::R'). cursor 2=c'+2 (c'=0). cfg cursor 4.
    --     (d+1)::R'_pred = R = 3::3::X++[1, 2]. d+1=3 (d=2). R'_pred = 3::X++[1, 2].
    --     Pred M [] 4 (2::3::X++[1, 2]). Use Level 3.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 2 := by omega
      have hR' : R'5 = 3 :: X ++ [1, 2] := hR_tail.symm
      subst hc'; subst hd; subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_2_3_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target L=[1] ✓ but R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D8: target cursor=a+3 ≥ 3 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D9: target M0 ⊥.
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D12: cursor 2=a+3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_multi_bounce_last_2_general a r' m_last L' middle_init _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (3 :: 3 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1], v=2. 4-case all ⊥.
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

/-- **Level 1: `M0 [2] (4 :: 3 :: X ++ [1, 2])` is not orbit-reachable**.
    D1 productive → Level 2. Other cases ⊥. Used to close #4 Case 2. -/
theorem OrbitReachable.not_M0_2_4_3_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] (4 :: 3 :: X ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). For target M0 [2] (4::3::X++[1, 2]):
    --     (a+1)::L' = [2] → a=1, L'=[]. (d+1)::R' = 4::3::X++[1, 2]. d+1=4 (d=3). R'=3::X++[1, 2].
    --     Pred M [1] 2 (3::3::X++[1, 2]). Use Level 2.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 1 := by omega
      have hd : d1 = 3 := by omega
      have hL' : L'1 = [] := hL_eq.symm
      have hR' : R'1 = 3 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_1_2_3_3_X_via_ih X (by rfl)
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
      have h_len : (4 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (4 :: 3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
-- Section 11: Chain helpers for #11 Case 2 (M [1, 6] 5 (d::R') step_R3)
-- ============================================================
-- Main chain (7 levels) for pred = M0 [2] (3 :: 5 :: X ++ [1, 2]):
--   L1 → D1 → L2 → D5 → L3 → D2 → L4 → D3 → L5 → D3 → L6 → D5 → L7
-- Plus sub-chains:
--   L5 D12: M0 [2, 2] (2::2::X++[1, 2]) → D1 → M [1, 2] 2 → D2 → M [1, 1, 2] 3 (terminal).
--   L5 sR3 Case 4: M0 [1, 2] (3::1::Y++[1, 2]) terminal.
--   L6 D12: M0 [4, 1] (2::1::X++[1, 2]) → D1 → M [3, 1] 2 (terminal).
--   L6 sR3 Case 4: M0 [3, 1] (3::1::Y++[1, 2]) → D1 → M [2, 1] 2 → D3 → M [1, 1] 4 (terminal).
--   L7 D2: closes via h_X_one (X all 1s → d=0 AllGe1 ⊥).
--   L7 sR3 Case 4: M0 [5] (3::1::Y++[1, 2]) → D1 → M [4] 2 → D3 → M [3] 4 (terminal).
-- Total: 19 helpers.

-- Sub-chain helpers (Y is parametric; closes via fixed structural 1s in R).

/-- **L7sR3c (terminal): `M [3] 4 (1 :: 1 :: Y ++ [1, 2])` is not orbit-reachable.** -/
theorem OrbitReachable.not_M_3_4_1_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [3] 4 (1 :: 1 :: Y ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: cursor a+1=4 (a=3). target.R=1::(d+1)::R'. R[1]=1 (d=0). AllGe1 ⊥.
    · injection htgt with _ _ hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: cursor 4=c'+2 (c'=2). cfg cursor c'+4=6. (a+1)::L'_pred=[3] → a=2. (d+1)=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with hd_eq _
      have hd : d3 = 0 := by omega
      subst hd
      subst hcfg'3
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    · exact MacroConfig.noConfusion htgt
    -- D5: target L=[1] vs [3] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target L=[1] vs [3] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target L=(a+4)::L' vs [3] → a+4=3 (a=-1) ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=4 (a=1). target.R=(d+1)::R'_pred=1::1::Y++[1, 2]. d+1=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with hd_eq _
      have hd : d12 = 0 := by omega
      subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have hd_ge := (AllGe1_cons.mp (AllGe1_cons.mp hAR).2).1
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R2_zero a L' h_pred_r2z =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    have ha : a = 0 := by omega
    subst ha
    have hAL := h_pred_r2z.macroInvariant.1
    have ha_ge := (AllGe1_cons.mp hAL).1
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[3], v=4. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([3] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([3] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · injection hLsuf.symm with h_head _; omega
    · -- a+4 = v = 4 → a = 0 AllGe1 ⊥.
      have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L7sR3b: `M [4] 2 (2 :: 1 :: Y ++ [1, 2])` is not orbit-reachable**. D3 → L7sR3c. -/
theorem OrbitReachable.not_M_4_2_2_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [4] 2 (2 :: 1 :: Y ++ [1, 2]))
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: cursor a+1=2 (a=1). target.R=1::(d+1)::R'. R[0]=1 vs cfg.R[0]=2 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: cursor 2=c'+2 (c'=0). cfg cursor c'+4=4. (a+1)::L'_pred=[4] → a=3. (d+1)=2 (d=1).
    --     R'_pred=1::Y++[1, 2]. Pred = M [3] 4 (1::1::Y++[1, 2]). Use L7sR3c.
    · injection htgt with hL hc hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have hc' : c'3 = 0 := by omega
      have ha : a3 = 3 := by omega
      have hL' : L'3 = [] := hL_eq.symm
      have hd : d3 = 1 := by omega
      have hR' : R'3 = 1 :: Y ++ [1, 2] := hR_tail.symm
      subst hc'; subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'3
      apply OrbitReachable.not_M_3_4_1_1_Y_via_ih Y (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[4] vs [1] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: cfg.L=[4] vs [1] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D8: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 (a=-2) ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cfg.L=[4]=(a+4)::L'_pred → a+4=4 (a=0) AllGe1 ⊥.
    · rename_i a11 z11 L'11 hcfg'11 _
      injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a11 = 0 := by omega
      subst ha
      subst hcfg'11
      mc_AllGe1_a_ge1
    -- D12: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- target M ((a+4)::L') (r+2) [1, 1]. cfg.L=[4]=(a+4)::L' → a+4=4 (a=0) AllGe1 ⊥.
    rename_i a r' L' h_pred_2as
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with ha _
    have ha0 : a = 0 := by omega
    subst ha0
    have hAL := h_pred_2as.macroInvariant.1
    have ha_ge := (AllGe1_cons.mp hAL).1
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | @step_multi_bounce_3run_last_2 a r' e L' h_pred_3run =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : ((r' + 1) :: (a + 4) :: L').length = ([4] : List Nat).length := by rw [hL]
    simp [List.length_cons] at h_len
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[4], v=2. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([4] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([4] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · -- Case 3: L_suf=(a+4)::L'=[4]. a+4 ≥ 5 (a≥1) but a+4=4 ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L7sR3a: `M0 [5] (3 :: 1 :: Y ++ [1, 2])` is not orbit-reachable**. D1 → L7sR3b.
    Used to close L7 step_R3 Case 4 (#11 Case 2 main chain). -/
theorem OrbitReachable.not_M0_5_3_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [5] (3 :: 1 :: Y ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [5] = (a+1)::L' → a=4, L'=[]. d+1=3 (d=2).
    --     R'=1::Y++[1, 2]. Pred = M [4] 2 (2::1::Y++[1, 2]). Use L7sR3b.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 4 := by omega
      have hd : d1 = 2 := by omega
      have hL' : L'1 = [] := hL_eq.symm
      have hR' : R'1 = 1 :: Y ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_4_2_2_1_Y_via_ih Y (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [5] ⊥.
    · injection htgt with hL _
      injection hL with hh _
      omega
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (3 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (3 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **L6sR3c (terminal): `M [1, 1] 4 (1 :: 1 :: Y ++ [1, 2])` is not orbit-reachable.** -/
theorem OrbitReachable.not_M_1_1_4_1_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [1, 1] 4 (1 :: 1 :: Y ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : ([1] : List Nat).length = (1 :: 1 :: Y ++ [1, 2]).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: cursor a+1=4 (a=3). target.R=1::(d+1)::R'. R[1]=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: cursor 4=c'+2 (c'=2). cfg cursor c'+4=6. (a+1)::L'_pred=[1, 1] → a=0 AllGe1.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[1, 1] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([1, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: cfg.L=[1, 1] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([1, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target L=(a+4)::L' vs [1, 1]. a+4=1 (a=-3) ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=4 (a=1). target.R=(d+1)::R'_pred=1::1::Y++[1, 2]. d+1=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with hd_eq _
      have hd : d12 = 0 := by omega
      subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have hd_ge := (AllGe1_cons.mp (AllGe1_cons.mp hAR).2).1
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_multi_bounce_2_double_shift a L' h_pred_2ds =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    have ha : a = 0 := by omega
    subst ha
    have hAL := h_pred_2ds.macroInvariant.1
    have ha_ge := (AllGe1_cons.mp hAL).1
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R2_zero a L' h_pred_r2z =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    have ha : a = 0 := by omega
    subst ha
    have hAL := h_pred_r2z.macroInvariant.1
    have ha_ge := (AllGe1_cons.mp hAL).1
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1, 1], v=4. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([1, 1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · -- Case 2: (r'+1)::(a+4)::L'=[1, 1]. a+4=1 (a=-3) ⊥. Or use AllGe1.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with _ hLsuf_tail
      injection hLsuf_tail with h_a4 _
      omega
    · injection hLsuf.symm with h_head _; omega
    · -- a+4 = v = 4 → a = 0 AllGe1 ⊥.
      have ha : a = 0 := by omega
      subst ha
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L6sR3b: `M [2, 1] 2 (2 :: 1 :: Y ++ [1, 2])` is not orbit-reachable**. D3 → L6sR3c. -/
theorem OrbitReachable.not_M_2_1_2_2_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [2, 1] 2 (2 :: 1 :: Y ++ [1, 2]))
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: target.R=1::(d+1)::R'. R[0]=1 vs 2 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: cursor 2=c'+2 (c'=0). cfg cursor c'+4=4. (a+1)::L'_pred=[2, 1] → a=1, L'_pred=[1].
    --     (d+1)=2 (d=1). R'_pred=1::Y++[1, 2]. Pred = M [1, 1] 4 (1::1::Y++[1, 2]). Use L6sR3c.
    · injection htgt with hL hc hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have hc' : c'3 = 0 := by omega
      have ha : a3 = 1 := by omega
      have hL' : L'3 = [1] := hL_eq.symm
      have hd : d3 = 1 := by omega
      have hR' : R'3 = 1 :: Y ++ [1, 2] := hR_tail.symm
      subst hc'; subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'3
      apply OrbitReachable.not_M_1_1_4_1_1_Y_via_ih Y (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[2, 1] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([2, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D6: cursor a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: cfg.L=[2, 1] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([2, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D8: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 (a=-2) ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cursor z+2=2 (z=0). cfg.L=[2, 1]=(a+4)::L'_pred → a+4=2 (a=-2) ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- target M ((a+4)::L') (r+2) [1, 1]. cfg.cursor=2=r+2 (r=0). cfg.L=[2, 1]=(a+4)::L'_pred → a+4=2 (a=-2) ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    -- target M ((r'+1)::(a+4)::L') (e+2) [1, 1]. cfg.L=[2, 1]=(r'+1)::(a+4)::L'_pred → r'+1=2 (r'=1), a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with _ hL_tail
    injection hL_tail with h_a4 _
    omega
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 1 :: Y ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[2, 1], v=2. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([2, 1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · -- Case 2: (r'+1)::(a+4)::L'=[2, 1]. a+4=1 (a=-3) ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with _ hLsuf_tail
      injection hLsuf_tail with h_a4 _
      omega
    · -- Case 3: (a+4)::L'=[2, 1]. a+4=2 (a=-2) ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L6sR3a: `M0 [3, 1] (3 :: 1 :: Y ++ [1, 2])` is not orbit-reachable**. D1 → L6sR3b.
    Used to close L6 step_R3 Case 4. -/
theorem OrbitReachable.not_M0_3_1_3_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [3, 1] (3 :: 1 :: Y ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [3, 1] = (a+1)::L' → a=2, L'=[1]. d+1=3 (d=2).
    --     R'=1::Y++[1, 2]. Pred = M [2, 1] 2 (2::1::Y++[1, 2]). Use L6sR3b.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 2 := by omega
      have hd : d1 = 2 := by omega
      have hL' : L'1 = [1] := hL_eq.symm
      have hR' : R'1 = 1 :: Y ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_2_1_2_2_1_Y_via_ih Y (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [3, 1] ⊥.
    · injection htgt with hL _
      have h_len : ([3, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (3 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (3 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **L6c (terminal): `M [3, 1] 2 (1 :: 1 :: X ++ [1, 2])` is not orbit-reachable.** Used in L6 D12 sub-chain. -/
theorem OrbitReachable.not_M_3_1_2_1_1_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M [3, 1] 2 (1 :: 1 :: X ++ [1, 2]))
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: cursor a+1=2 (a=1). target.R=1::(d+1)::R'. R[1]=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq _
      have hd : d2 = 0 := by omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: cursor 2=c'+2 (c'=0). cfg cursor c'+4=4. (a+1)::L'_pred=[3, 1] → a=2, L'_pred=[1].
    --     (d+1)::R'_pred=1::1::X++[1, 2]. d+1=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with hd_eq _
      have hd : d3 = 0 := by omega
      subst hd
      subst hcfg'3
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[3, 1] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([3, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D6: cursor a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: cfg.L=[3, 1] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([3, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D8: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 (a=-2) ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cursor z+2=2 (z=0). cfg.L=[3, 1]=(a+4)::L'_pred → a+4=3 (a=-1) ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- target M ((a+4)::L') (r+2) [1, 1]. cfg.L=[3, 1]=(a+4)::L'_pred → a+4=3 (a=-1) ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    -- target.L = (r'+1)::(a+4)::L' = [3, 1]. r'+1=3, a+4=1 (a=-3) ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with _ hL_tail
    injection hL_tail with h_a4 _
    omega
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    -- target M ((a+4)::L') (r+2) [1, 1, 1]. cfg.L=[3, 1]=(a+4)::L'_pred → a+4=3 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[3, 1], v=2. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([3, 1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · -- Case 2: (r'+1)::(a+4)::L'=[3, 1]. a+4=1 ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with _ hLsuf_tail
      injection hLsuf_tail with h_a4 _
      omega
    · -- Case 3: (a+4)::L'=[3, 1]. a+4=3 (a=-1) ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L6b: `M0 [4, 1] (2 :: 1 :: X ++ [1, 2])` is not orbit-reachable**. D1 → L6c.
    Used to close L6 D12 sub-chain. -/
theorem OrbitReachable.not_M0_4_1_2_1_X_via_ih (X : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [4, 1] (2 :: 1 :: X ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [4, 1] = (a+1)::L' → a=3, L'=[1]. d+1=2 (d=1).
    --     R'=1::X++[1, 2]. Pred = M [3, 1] 2 (1::1::X++[1, 2]). Use L6c.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 3 := by omega
      have hd : d1 = 1 := by omega
      have hL' : L'1 = [1] := hL_eq.symm
      have hR' : R'1 = 1 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_3_1_2_1_1_X_via_ih X (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [4, 1] ⊥.
    · injection htgt with hL _
      have h_len : ([4, 1] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (2 :: 1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **L5sR3 (terminal): `M0 [1, 2] (3 :: 1 :: Y ++ [1, 2])` is not orbit-reachable.**
    Used to close L5 step_R3 Case 4. -/
theorem OrbitReachable.not_M0_1_2_3_1_Y_via_ih (Y : List Nat) {cfg : MacroConfig}
    (hcfg : cfg = .M0 [1, 2] (3 :: 1 :: Y ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [1, 2] = (a+1)::L' → a=0 AllGe1 ⊥.
    · injection htgt with hL _
      injection hL with ha_eq _
      have ha : a1 = 0 := by omega
      subst ha
      subst hcfg'1
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [1, 2] ⊥.
    · injection htgt with hL _
      have h_len : ([1, 2] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (3 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (3 :: 1 :: Y ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **L5d (terminal): `M [1, 1, 2] 3 (1 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s).
    Used in L5 D12 sub-chain. -/
theorem OrbitReachable.not_M_1_1_2_3_1_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [1, 1, 2] 3 (1 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    have h_len : ([1] : List Nat).length = ([1, 1, 2] : List Nat).length := by rw [hL]
    simp [List.length_cons] at h_len
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: target M L' (a+1) (1::(d+1)::R'). cursor a+1=3 (a=2). target.L=[1, 1, 2]=L'_pred.
    --     R: 1::(d+1)::R'_pred=1::X++[1, 2]. R[0]=1 ✓. (d+1)::R'_pred=X++[1, 2].
    --     Need d2=0 via h_X_one. Then AllGe1 ⊥.
    · injection htgt with _ _ hR
      injection hR with _ hR_tail
      -- hR_tail : (d2+1)::R'2 = X ++ [1, 2]. With h_X_one, X[0]=1 (or X=[]), so d2+1=1, d2=0.
      have hd : d2 = 0 := by
        cases X with
        | nil =>
          injection hR_tail with hd_eq _
          omega
        | cons h X' =>
          have hh : h = 1 := h_X_one h (by simp)
          injection hR_tail with hd_eq _
          omega
      subst hd
      subst hcfg'2
      have hAR := h_prev.macroInvariant.2.2.1
      have hd_ge := (AllGe1_cons.mp hAR).1
      omega
    -- D3: cursor 3=c'+2 (c'=1). cfg cursor c'+4=5. (a+1)::L'_pred=[1, 1, 2] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[1, 1, 2] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([1, 1, 2] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D6: cursor a+4 ≥ 4 ≠ 3 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: cfg.L=[1, 1, 2] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([1, 1, 2] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D8: cursor a+3=3 (a=0). cfg.L=[1, 1, 2]=L'_pred (in pred M0 (a::L') [2]). target.R=[1] vs cfg.R len ≥ 3 ⊥.
    · injection htgt with _ _ hR
      have h_len : (1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=3 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cfg.L=[1, 1, 2]=(a+4)::L'_pred → a+4=1 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=3 (a=0) AllGe1 ⊥.
    · injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- target.L=(a+4)::L' vs [1, 1, 2] → a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    -- target.L=(r'+1)::(a+4)::L' vs [1, 1, 2]. r'+1=1 (r'=0), a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with _ hL_tail
    injection hL_tail with h_a4 _
    omega
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    -- target.L=(a+4)::L' vs [1, 1, 2] → a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1, 1, 2], v=3. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · -- Case 1: mi_A.reverse++e::(r'+1)::(a+4)::L'=[1, 1, 2]. Length: |mi_A|+3+|L'|=3.
      -- mi_A=[], L'=[]. Then e::(r'+1)::(a+4)::[]=[e, r'+1, a+4]=[1, 1, 2].
      -- a+4=2 (a=-2) ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([1, 1, 2] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      have hmi_len : mi_A.length = 0 := by omega
      have hL'_len : L'.length = 0 := by omega
      have hmi_eq : mi_A = [] := List.eq_nil_of_length_eq_zero hmi_len
      have hL'_eq : L' = [] := List.eq_nil_of_length_eq_zero hL'_len
      subst hmi_eq
      subst hL'_eq
      simp only [List.reverse_nil, List.nil_append] at hLsuf
      -- hLsuf : [1, 1, 2] = e :: (r' + 1) :: (a + 4) :: []
      injection hLsuf.symm with _ hLsuf_tail
      injection hLsuf_tail with _ hLsuf_tail2
      injection hLsuf_tail2 with h_a4 _
      omega
    · -- Case 2: (r'+1)::(a+4)::L'=[1, 1, 2]. r'+1=1, a+4=1 ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with _ hLsuf_tail
      injection hLsuf_tail with h_a4 _
      omega
    · -- Case 3: (a+4)::L'=[1, 1, 2]. a+4=1 ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · -- Case 4: a+4=v=3 (a=-1) ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L5c: `M [1, 2] 2 (1 :: 2 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s). D2 → L5d. -/
theorem OrbitReachable.not_M_1_2_2_1_2_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [1, 2] 2 (1 :: 2 :: X ++ [1, 2]))
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
    | ⟨a2, L'2, d2, R'2, hcfg'2, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: cursor a+1=2 (a=1). cfg.L=[1, 2]=L'_pred. target.R=1::(d+1)::R'_pred=1::2::X++[1, 2].
    --     R[0]=1 ✓. (d+1)=2 (d=1). R'_pred=X++[1, 2]. Pred = M [1, 1, 2] 3 (1::X++[1, 2]). Use L5d.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR_tail2
      have ha : a2 = 1 := by omega
      have hL' : L'2 = [1, 2] := hL.symm
      have hd : d2 = 1 := by omega
      have hR' : R'2 = X ++ [1, 2] := hR_tail2.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'2
      apply OrbitReachable.not_M_1_1_2_3_1_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D3: cursor c'+2=2 (c'=0). cfg cursor c'+4=4. (a+1)::L'_pred=[1, 2] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[1, 2] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([1, 2] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D6: cursor a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: cfg.L=[1, 2] vs [1] ⊥.
    · injection htgt with hL _ _
      have h_len : ([1, 2] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    -- D8: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4=2 (a=-2) ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cfg.L=[1, 2]=(a+4)::L'_pred → a+4=1 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=2 (a=-1) ⊥.
    · injection htgt with _ hc _
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- target.L=(a+4)::L' vs [1, 2] → a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_multi_bounce_3run_last_2 _ =>
    -- target.L=(r'+1)::(a+4)::L' vs [1, 2]. r'+1=1, a+4=2 (a=-2) ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with _ hL_tail
    injection hL_tail with h_a4 _
    omega
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 2 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    -- target.L=(a+4)::L' vs [1, 2] → a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1, 2], v=2. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([1, 2] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · -- Case 2: (r'+1)::(a+4)::L'=[1, 2]. r'+1=1 (r'=0), a+4=2 (a=-2) ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with _ hLsuf_tail
      injection hLsuf_tail with h_a4 _
      omega
    · -- Case 3: (a+4)::L'=[1, 2]. a+4=1 ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L5b: `M0 [2, 2] (2 :: 2 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s). D1 → L5c.
    Used to close L5 D12 sub-chain. -/
theorem OrbitReachable.not_M0_2_2_2_2_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2, 2] (2 :: 2 :: X ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [2, 2]=(a+1)::L' → a=1, L'=[2]. d+1=2 (d=1).
    --     R'=2::X++[1, 2]. Pred = M [1, 2] 2 (1::2::X++[1, 2]). Use L5c.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 1 := by omega
      have hd : d1 = 1 := by omega
      have hL' : L'1 = [2] := hL_eq.symm
      have hR' : R'1 = 2 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_1_2_2_1_2_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D4: target M0 [1] (...). L=[1] vs [2, 2] ⊥.
    · injection htgt with hL _
      have h_len : ([2, 2] : List Nat).length = ([1] : List Nat).length := by rw [hL]
      simp [List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    -- D9: target R=[1] mismatch.
    · injection htgt with _ hR
      have h_len : (2 :: 2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (2 :: 2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
-- Section 11 main chain: Levels 7 → 1 (each uses h_X_one for X all 1s)
-- ============================================================

/-- **L7 (main): `M [] 9 (1 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s).
    D2 closes via h_X_one. step_R3 Case 4 → L7sR3a (M0 [5]). -/
theorem OrbitReachable.not_M_empty_9_1_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [] 9 (1 :: X ++ [1, 2]))
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
    -- D2: cursor a+1=9 (a=8). target.L=L'_pred=[]. R: 1::(d+1)::R'_pred=1::X++[1, 2].
    --     R[0]=1 ✓. (d+1)::R'_pred=X++[1, 2]. With h_X_one, d=0 → AllGe1 ⊥.
    · injection htgt with hL _ hR
      injection hR with _ hR_tail
      have hd : d2 = 0 := by
        cases X with
        | nil =>
          injection hR_tail with hd_eq _
          omega
        | cons h X' =>
          have hh : h = 1 := h_X_one h (by simp)
          injection hR_tail with hd_eq _
          omega
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
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target L=[1] vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (1 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: target L=(a+4)::L' vs [] ⊥.
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: cursor a+3=9 (a=6). target.L=[]=L'_pred. (d+1)::R'_pred=1::X++[1, 2]. d+1=1 (d=0) AllGe1.
    · rename_i a12 L'12 d12 R'12 hcfg'12 _
      injection htgt with _ _ hR
      injection hR with hd_eq _
      have hd : d12 = 0 := by omega
      subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have hd_ge := (AllGe1_cons.mp (AllGe1_cons.mp hAR).2).1
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    -- cfg.R = 1::X++[1, 2] vs target.R = [1, 1, 1]. For X=[]: differs in last elt; for X≠[]: length differs.
    cases X with
    | nil =>
      injection hR with _ hR_tail
      injection hR_tail with _ hR_tail2
      injection hR_tail2 with hh _
      omega
    | cons h X' =>
      have h_len : (1 :: h :: X' ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
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
    -- cfg.R = 1::X++[1, 2]. For X=[]: length 3 vs 4 ⊥. For X≠[]: length ≥ 4. For X=[h]: length 4 = 4 match needed; check elt.
    cases X with
    | nil =>
      have h_len : (1 :: ([] : List Nat) ++ [1, 2]).length = ([1, 1, 1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    | cons h X' =>
      cases X' with
      | nil =>
        -- X=[h], cfg.R=[1, h, 1, 2] vs [1, 1, 1, 1]. Last elt 2 vs 1 ⊥.
        injection hR with _ hR_tail
        injection hR_tail with _ hR_tail2
        injection hR_tail2 with _ hR_tail3
        injection hR_tail3 with hh _
        omega
      | cons h2 X'' =>
        have h_len : (1 :: h :: h2 :: X'' ++ [1, 2]).length = ([1, 1, 1, 1] : List Nat).length := by rw [hR]
        simp [List.length_append, List.length_cons] at h_len
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[], v=9. Cases 1-3: empty L_suf ⊥. Case 4: a+4=9 (a=5), L'=[], pred M0 [5].
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, hR_eq⟩ := hcfg
    subst hL_eq
    subst hv_eq
    subst hR_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨h_mi_one, h_e, hr', hav, hLsuf⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
    · exact absurd hLsuf.symm (List.cons_ne_nil _ _)
    · exact absurd hLsuf.symm (List.cons_ne_nil _ _)
    · -- Case 4: a+4=9 (a=5), L'=[], r'=0, e=1, middle_init Y all 1s.
      -- Pred = M0 [5] (3::1::Y++[1, 2]). Use L7sR3a.
      have ha : a = 5 := by omega
      subst ha
      have hL'' : L' = [] := hLsuf.symm
      subst hL''
      subst hr'
      subst h_e
      apply OrbitReachable.not_M0_5_3_1_Y_via_ih middle_init (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt h_phi_side ⊢
          omega)
        h_prev_R3
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L6 (main): `M [1] 7 (2 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s).
    D5 → L7. D12 → L6b. step_R3 Case 4 → L6sR3a. -/
theorem OrbitReachable.not_M_1_7_2_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 7 (2 :: X ++ [1, 2]))
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
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    · exact MacroConfig.noConfusion htgt
    -- D2: cursor a+1=7 (a=6). cfg.L=[1]=L'_pred. target.R=1::(d+1)::R' vs cfg.R=2::X++[1, 2]. R[0]=1 vs 2 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: cursor c'+2=7 (c'=5). cfg cursor c'+4=9. (a+1)::L'_pred=[1] → a=0 AllGe1 ⊥.
    · injection htgt with hL _ _
      injection hL with ha_eq _
      have ha : a3 = 0 := by omega
      subst ha
      subst hcfg'3
      mc_AllGe1_a_ge1
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[1] ✓. cursor c'+2=7 (c'=5). cfg cursor c'+4=9. (d+1)::R'_pred=2::X++[1, 2].
    --     d+1=2 (d=1). R'_pred=X++[1, 2]. Pred = M [] 9 (1::X++[1, 2]). Use L7.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 5 := by omega
      have hd : d5 = 1 := by omega
      have hR' : R'5 = X ++ [1, 2] := hR_tail.symm
      subst hc'; subst hd; subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_9_1_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: cfg.L=[1] ✓. target M [1] (a+4) [1]. cfg.cursor 7 = a+4 (a=3). target.R=[1] vs len ≥ 4 ⊥.
    · injection htgt with _ _ hR
      have h_len : (2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D8: cursor a+3=7 (a=4). target.R=[1] vs len ≥ 4 ⊥.
    · injection htgt with _ _ hR
      have h_len : (2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: cursor z+2=7 (z=5). cfg.L=[1]=(a+4)::L'_pred → a+4=1 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=7 (a=4). cfg.L=[1]=L'_pred. (d+1)::R'_pred=2::X++[1, 2]. d+1=2 (d=1).
    --     R'_pred=X++[1, 2]. Pred = M0 [4, 1] (2::1::X++[1, 2]). Use L6b.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 4 := by omega
      have hL' : L'12 = [1] := hL.symm
      have hd : d12 = 1 := by omega
      have hR' : R'12 = X ++ [1, 2] := hR_tail.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_4_1_2_1_X_via_ih X (by rfl)
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
    have h_len : (2 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    -- target.R=[1, 1] vs cfg.R[0]=2 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
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
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    -- target M ((a+4)::L') (r+2) [1, 1, 1]. cfg.L=[1]=(a+4)::L'_pred → a+4=1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[1], v=7. Cases 1-3: shape ⊥. Case 4: a+4=7 (a=3), L'=[1], pred M0 [3, 1].
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨h_mi_one, h_e, hr', hav, hLsuf⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([1] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · -- Case 3: L_suf=(a+4)::L'=[1]. a+4=1 ⊥ (a≥1).
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · -- Case 4: a+4=7 (a=3), L'=[1], pred = M0 [3, 1] (3::1::Y++[1, 2]). Use L6sR3a.
      have ha : a = 3 := by omega
      subst ha
      have hL'' : L' = [1] := hLsuf.symm
      subst hL''
      subst hr'
      subst h_e
      apply OrbitReachable.not_M0_3_1_3_1_Y_via_ih middle_init (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt h_phi_side ⊢
          omega)
        h_prev_R3
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L5 (main): `M [2] 5 (3 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s).
    D3 → L6. D12 → L5b. step_R3 Case 4 → L5sR3. -/
theorem OrbitReachable.not_M_2_5_3_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [2] 5 (3 :: X ++ [1, 2]))
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
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨_, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, htgt⟩
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    · exact MacroConfig.noConfusion htgt
    -- D2: target.R=1::(d+1)::R' vs 3::X++[1, 2]. R[0]=1 vs 3 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: cursor c'+2=5 (c'=3). cfg cursor c'+4=7. (a+1)::L'_pred=[2] → a=1, L'_pred=[].
    --     (d+1)::R'_pred=3::X++[1, 2]. d+1=3 (d=2). R'_pred=X++[1, 2]. Pred = M [1] 7 (2::X++[1, 2]). Use L6.
    · injection htgt with hL hc hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have hc' : c'3 = 3 := by omega
      have ha : a3 = 1 := by omega
      have hL' : L'3 = [] := hL_eq.symm
      have hd : d3 = 2 := by omega
      have hR' : R'3 = X ++ [1, 2] := hR_tail.symm
      subst hc'; subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'3
      apply OrbitReachable.not_M_1_7_2_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[2] vs [1] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: cfg.L=[2] vs [1] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (3 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D11: cursor z+2=5 (z=3). cfg.L=[2]=(a+4)::L'_pred → a+4=2 ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=5 (a=2). cfg.L=[2]=L'_pred. (d+1)::R'_pred=3::X++[1, 2]. d+1=3 (d=2).
    --     R'_pred=X++[1, 2]. Pred = M0 [2, 2] (2::2::X++[1, 2]). Use L5b.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have ha : a12 = 2 := by omega
      have hL' : L'12 = [2] := hL.symm
      have hd : d12 = 2 := by omega
      have hR' : R'12 = X ++ [1, 2] := hR_tail.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'12
      apply OrbitReachable.not_M0_2_2_2_2_X_via_ih X h_X_one (by rfl)
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
    have h_len : (3 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
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
    -- target.R=[1, 1, 1, 1] vs cfg.R=3::X++[1, 2]. R[0]=3 vs 1 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_R2_succ _ =>
    -- target M ((a+4)::L') (r+2) [1, 1, 1]. cfg.L=[2]=(a+4)::L'_pred → a+4=2 ⊥.
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[2], v=5. Cases 1-3: shape ⊥. Case 4: a+4=5 (a=1), L'=[2], pred M0 [1, 2].
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨h_mi_one, h_e, hr', hav, hLsuf⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([2] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([2] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · -- Case 3: a+4 ≥ 5 vs 2 ⊥.
      have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · -- Case 4: a+4=5 (a=1), L'=[2], pred = M0 [1, 2] (3::1::Y++[1, 2]). Use L5sR3.
      have ha : a = 1 := by omega
      subst ha
      have hL'' : L' = [2] := hLsuf.symm
      subst hL''
      subst hr'
      subst h_e
      apply OrbitReachable.not_M0_1_2_3_1_Y_via_ih middle_init (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt h_phi_side ⊢
          omega)
        h_prev_R3
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L4 (main): `M [3] 3 (4 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s). D3 → L5. -/
theorem OrbitReachable.not_M_3_3_4_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [3] 3 (4 :: X ++ [1, 2]))
    (h_excl_R1_pred : ∀ {d_pre : Nat} {R'_pre : List Nat},
       OrbitReachable (.M [] 3 (d_pre :: R'_pre)) →
       (MacroConfig.M [] 3 (d_pre :: R'_pre)).phi < cfg.phi → False) :
    ¬ OrbitReachable cfg := by
  intro h_or
  cases h_or with
  | init =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | step_macro h_prev h_step =>
    rw [hcfg] at h_step
    rcases macroStep_eq_some_cases _ _ _ h_step with
      ⟨_, _, _, _, _, _, htgt⟩
    | ⟨_, _, _, _, _, _, htgt⟩
    | ⟨a3, c'3, L'3, d3, R'3, hcfg'3, _, htgt⟩
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
    -- D2: target.R=1::(d+1)::R' vs 4::X++[1, 2]. R[0]=1 vs 4 ⊥.
    · injection htgt with _ _ hR
      injection hR with hh _
      omega
    -- D3: cursor c'+2=3 (c'=1). cfg cursor c'+4=5. (a+1)::L'_pred=[3] → a=2, L'_pred=[].
    --     (d+1)::R'_pred=4::X++[1, 2]. d+1=4 (d=3). R'_pred=X++[1, 2]. Pred = M [2] 5 (3::X++[1, 2]). Use L5.
    · injection htgt with hL hc hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have hc' : c'3 = 1 := by omega
      have ha : a3 = 2 := by omega
      have hL' : L'3 = [] := hL_eq.symm
      have hd : d3 = 3 := by omega
      have hR' : R'3 = X ++ [1, 2] := hR_tail.symm
      subst hc'; subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'3
      apply OrbitReachable.not_M_2_5_3_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    · exact MacroConfig.noConfusion htgt
    -- D5: cfg.L=[3] vs [1] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D6: cursor a+4 ≥ 4 ≠ 3 ⊥.
    · injection htgt with _ hc _
      omega
    -- D7: cfg.L=[3] vs [1] ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D8: cursor a+3=3 (a=0). target.R=[1] vs cfg.R len ≥ 4 ⊥.
    · injection htgt with _ _ hR
      have h_len : (4 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: cursor a+4 ≥ 4 ≠ 3 ⊥.
    · injection htgt with _ hc _
      omega
    -- D11: cfg.L=[3]=(a+4)::L'_pred → a+4=3 (a=-1) ⊥.
    · injection htgt with hL _ _
      injection hL with hh _
      omega
    -- D12: cursor a+3=3 (a=0) AllGe1 ⊥.
    · injection htgt with _ hc _
      have ha : a12 = 0 := by omega
      subst ha
      subst hcfg'12
      mc_AllGe1_a_ge1
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | step_multi_bounce_3run_last_2 _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    injection hR with hh _
    omega
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (4 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    injection hL with hh _
    omega
  | @step_R3 a r' e L' middle_init _ _ h_prev_R3 _ _ _ h_safe h_strict_safe h_phi_side =>
    -- L_suf=[3], v=3. All 4 cases close.
    mc_R3_extract
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨mi_A, _, _, _, hLsuf⟩ |
      ⟨_, _, hLsuf⟩ | ⟨_, _, _, hLsuf⟩ | ⟨_, _, _, hav, _⟩
    · have h_len :
          (mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L').length = ([3] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_append, List.length_cons] at h_len
      omega
    · have h_len :
          ((r' + 1) :: (a + 4) :: L').length = ([3] : List Nat).length := by
        rw [← hLsuf]
      simp [List.length_cons] at h_len
    · have hAL := h_prev_R3.macroInvariant.1
      have ha_ge := (AllGe1_cons.mp hAL).1
      injection hLsuf.symm with h_head _
      omega
    · omega
  | step_R1 h_pred _ _ _ h_phi =>
    mc_R1_callback

/-- **L3 (main): `M [] 4 (1 :: 5 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s). D2 → L4. -/
theorem OrbitReachable.not_M_empty_4_1_5_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [] 4 (1 :: 5 :: X ++ [1, 2]))
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
    | ⟨a12, L'12, d12, R'12, hcfg'12, _, htgt⟩
    · exact MacroConfig.noConfusion htgt
    -- D2: cursor a+1=4 (a=3). target.L=[]=L'_pred. R: 1::(d+1)::R'_pred=1::5::X++[1, 2].
    --     R[0]=1 ✓. (d+1)=5 (d=4). R'_pred=X++[1, 2]. Pred = M [3] 3 (4::X++[1, 2]). Use L4.
    · injection htgt with hL hc hR
      injection hR with _ hR_tail
      injection hR_tail with hd_eq hR_tail2
      have ha : a2 = 3 := by omega
      have hL' : L'2 = [] := hL.symm
      have hd : d2 = 4 := by omega
      have hR' : R'2 = X ++ [1, 2] := hR_tail2.symm
      subst ha; subst hL'; subst hd; subst hR'
      subst hcfg'2
      apply OrbitReachable.not_M_3_3_4_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
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
    · injection htgt with _ _ hR
      have h_len : (1 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · injection htgt with _ _ hR
      have h_len : (1 :: 5 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · injection htgt with hL _ _
      exact (List.cons_ne_nil _ _) hL.symm
    -- D12: cursor a+3=4 (a=1). target.L=[]=L'_pred. (d+1)::R'_pred=1::5::X++[1, 2]. d+1=1 (d=0) AllGe1.
    · injection htgt with _ _ hR
      injection hR with hd_eq _
      have hd : d12 = 0 := by omega
      subst hd
      subst hcfg'12
      have hAR := h_prev.macroInvariant.2.1
      have hd_ge := (AllGe1_cons.mp (AllGe1_cons.mp hAR).2).1
      omega
  | step_multi_bounce_general _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_multi_bounce_general_to_zero _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact (List.cons_ne_nil _ _) hL
  | step_multi_bounce_2_double_shift _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (1 :: 5 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    injection hR with _ hR_tail
    injection hR_tail with hh _
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

/-- **L2 (main): `M [1] 2 (2 :: 5 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s). D5 → L3. -/
theorem OrbitReachable.not_M_1_2_2_5_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M [1] 2 (2 :: 5 :: X ++ [1, 2]))
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
    -- D2: target.R=1::(d+1)::R' vs 2::5::X++[1, 2]. R[0]=1 vs 2 ⊥.
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
    -- D5: cfg.L=[1] ✓. cursor c'+2=2 (c'=0). cfg cursor c'+4=4. (d+1)::R'_pred=2::5::X++[1, 2].
    --     d+1=2 (d=1). R'_pred=5::X++[1, 2]. Pred = M [] 4 (1::5::X++[1, 2]). Use L3.
    · injection htgt with hL hc hR
      injection hR with hd_eq hR_tail
      have hc' : c'5 = 0 := by omega
      have hd : d5 = 1 := by omega
      have hR' : R'5 = 5 :: X ++ [1, 2] := hR_tail.symm
      subst hc'; subst hd; subst hR'
      subst hcfg'5
      apply OrbitReachable.not_M_empty_4_1_5_X_via_ih X h_X_one (by rfl)
        (h_excl_R1_pred := fun {d_pre} {R'_pre} h_or_pre h_phi_lt => by
          apply h_excl_R1_pred h_or_pre
          rw [hcfg]
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
            List.sum_append, List.sum_cons, List.sum_nil] at h_phi_lt ⊢
          omega)
        h_prev
    -- D6: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    -- D7: target M [1] (a+4) [1]. cursor a+4 ≥ 4 ≠ 2 ⊥.
    · injection htgt with _ hc _
      omega
    -- D8: target R=[1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    -- D10: target R=[1, 1] mismatch.
    · injection htgt with _ _ hR
      have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
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
    have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
    have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | @step_multi_bounce_last_2_general _ _ _ _ _ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
  | step_R2_zero _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, hc, _⟩ := hcfg
    omega
  | step_R2_succ _ =>
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨_, _, hR⟩ := hcfg
    have h_len : (2 :: 5 :: X ++ [1, 2]).length = ([1, 1, 1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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

/-- **L1 (main, top): `M0 [2] (3 :: 5 :: X ++ [1, 2])` is not orbit-reachable** (X all 1s).
    D1 → L2. Used to close #11 Case 2 step_R3 sub-case in d2.lean. -/
theorem OrbitReachable.not_M0_2_3_5_X_via_ih (X : List Nat) (h_X_one : ∀ x ∈ X, x = 1)
    {cfg : MacroConfig}
    (hcfg : cfg = .M0 [2] (3 :: 5 :: X ++ [1, 2]))
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
    -- D1: target M0 ((a+1)::L') ((d+1)::R'). [2]=(a+1)::L' → a=1, L'=[]. d+1=3 (d=2).
    --     R'=5::X++[1, 2]. Pred = M [1] 2 (2::5::X++[1, 2]). Use L2.
    · injection htgt with hL hR
      injection hL with ha_eq hL_eq
      injection hR with hd_eq hR_tail
      have ha : a1 = 1 := by omega
      have hd : d1 = 2 := by omega
      have hL' : L'1 = [] := hL_eq.symm
      have hR' : R'1 = 5 :: X ++ [1, 2] := hR_tail.symm
      subst ha; subst hd; subst hL'; subst hR'
      subst hcfg'1
      apply OrbitReachable.not_M_1_2_2_5_X_via_ih X h_X_one (by rfl)
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
      have h_len : (3 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
      simp [List.length_append, List.length_cons] at h_len
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
    · exact MacroConfig.noConfusion htgt
  | step_multi_bounce_general _ =>
    exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_general_to_zero _ =>
    rw [MacroConfig.M0.injEq] at hcfg
    obtain ⟨_, hR⟩ := hcfg
    have h_len : (3 :: 5 :: X ++ [1, 2]).length = ([1] : List Nat).length := by rw [hR]
    simp [List.length_append, List.length_cons] at h_len
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
