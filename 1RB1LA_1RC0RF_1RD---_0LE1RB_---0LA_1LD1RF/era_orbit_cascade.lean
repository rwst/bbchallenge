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
    rw [hcfg_M] at hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, _⟩
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    -- L_suf = [3], v = 2. h_disj: ∃ x ∈ [3], x ≥ 5 ⊥. v = a+4 = 2 ⊥ (Nat).
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
    rw [hcfg_M] at hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, hR_eq⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨x, hx, _⟩ | ⟨h_v_eq, hL_eq⟩
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
    rw [hcfg_M] at hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL_eq, hv_eq, _⟩ := hcfg
    subst hL_eq
    subst hv_eq
    rcases h_disj with ⟨x, hx, hx_ge⟩ | ⟨h_v_eq, hL_eq⟩
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
    -- L_suf = [2], v = 2. h_disj: ∃ x ∈ [2], x ≥ 5 (2 < 5) ⊥. v = a+4 = 2 ⊥.
    obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
    rw [hcfg_M] at hcfg
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
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
  | step_R3 _ _ _ _ _ h_strict_safe _ =>
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


end Sweeper
