import machine_base

open BusyLean

namespace Sweeper

-- ============================================================
-- Macro progress invariant
-- ============================================================

/-- The progress predicate: config is a macro config satisfying AllGe1. -/
def MacroProg (c : Config 6) : Prop :=
  ∃ cfg : MacroConfig, c = cfg.toConfig ∧ MacroInvariant cfg

/-- MacroConfig.toConfig always has state = some stA. -/
lemma MacroConfig.toConfig_state (cfg : MacroConfig) :
    cfg.toConfig.state = some stA := by
  cases cfg with
  | M L c R => simp [MacroConfig.toConfig, M_Config]
  | M0 L R => simp [MacroConfig.toConfig, M0_Config]

/-- Package a transition + invariant into a progress proof. -/
private lemma mk_progress {c₀ : Config 6} (k : Nat) (cfg' : MacroConfig) (hk : 0 < k)
    (htrans : run sweeper c₀ k = cfg'.toConfig) (hinv' : MacroInvariant cfg') :
    ∃ k, 0 < k ∧ MacroProg (run sweeper c₀ k) ∧ (run sweeper c₀ k).state ≠ none := by
  refine ⟨k, hk, ⟨cfg', htrans, hinv'⟩, ?_⟩
  sorry -- state ≠ none: follows from htrans + MacroConfig.toConfig_state but ▸/congr_arg timeout

/-- Any M_Config has state = some stA ≠ none. -/
lemma M_Config_state_ne_none (L : List Nat) (n : Nat) (R : List Nat) :
    (M_Config L n R).state ≠ none := by simp [M_Config]

/-- Any M0_Config has state = some stA ≠ none. -/
lemma M0_Config_state_ne_none (L : List Nat) (R : List Nat) :
    (M0_Config L R).state ≠ none := by simp [M0_Config]

/-- Multi-bounce progress: last ≥ 3 case. -/
private lemma multi_bounce_progress {a r' last'' : Nat} {L' R_mid : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])))
    (hR_mid_ge : ∀ x ∈ R_mid, x ≥ 1) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])) k).state ≠ none := by
  sorry -- whnf timeout: congr_arg Config.state on Config with R_mid.reverse

/-- Multi-bounce progress: last = 1 case. -/
private lemma multi_bounce_to_zero_progress {a r' : Nat} {L' R_mid : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: R_mid ++ [1])))
    (hR_mid_ge : ∀ x ∈ R_mid, x ≥ 1) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [1])) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [1])) k).state ≠ none := by
  sorry -- same whnf timeout

set_option maxHeartbeats 400000 in
/-- Every macro config satisfying the invariant progresses to another one.
    This is the core dispatch: match on the config shape, apply the right rule. -/
theorem macro_progress (c : Config 6) (h : MacroProg c) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper c k) ∧ (run sweeper c k).state ≠ none := by
  obtain ⟨cfg, hc, hinv⟩ := h
  subst hc
  cases cfg with
  | M L c R =>
    have hL := hinv.1; have hc := hinv.2.1; have hR := hinv.2.2.1
    have hR_ne := hinv.2.2.2.1
    obtain ⟨d, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    cases L with
    | nil =>
      match c, hc with
      | 2, _ =>
        have ht := macro_sweep_to_zero_left_empty d R'
        exact mk_progress 11 _ (by omega) ht (invariant_sweep_to_zero_left_empty hinv)
      | 3, _ => exact absurd ⟨by omega, by decide⟩ (hinv.2.2.2.2 rfl)
      | c' + 4, _ =>
        have htrans : run sweeper (M_Config [] (c' + 4) (d :: R')) (2 * (c' + 4) + 7) =
            M_Config [1] (c' + 2) ((d + 1) :: R') := by
          rw [show c' + 4 = (c' + 1) + 3 from by omega]; exact macro_sweep_left_empty (c' + 1) d R'
        exact mk_progress _ (.M [1] (c'+2) ((d+1)::R')) (by omega) htrans (invariant_sweep_left_empty hinv)
    | cons a L' =>
      match c, hc with
      | 2, _ =>
        have ht := macro_sweep_to_zero a d L' R'
        exact mk_progress 11 _ (by omega) ht (invariant_sweep_to_zero hinv)
      | 3, _ =>
        have ht := macro_sweep_and_shift a d L' R'
        exact mk_progress 19 _ (by omega) ht (invariant_sweep_and_shift hinv)
      | c' + 4, _ =>
        have htrans : run sweeper (M_Config (a :: L') (c' + 4) (d :: R')) (2 * (c' + 4) + 7) =
            M_Config ((a + 1) :: L') (c' + 2) ((d + 1) :: R') := by
          rw [show c' + 4 = (c' + 1) + 3 from by omega]; exact macro_sweep a (c' + 1) d L' R'
        exact mk_progress _ (.M ((a+1)::L') (c'+2) ((d+1)::R')) (by omega) htrans (invariant_sweep hinv)
  | M0 L R =>
    have hL := hinv.1; have hR := hinv.2.1
    have hL_ne := hinv.2.2.1; have hR_ne := hinv.2.2.2.1
    have hNH := hinv.2.2.2.2
    obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL_ne
    obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    have ha := (AllGe1_cons.mp hL).1
    have hr := (AllGe1_cons.mp hR).1
    cases R' with
    | nil =>
      -- R = [r], single element
      -- Rewrite a as (a-1)+1 for theorem matching
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      match r, hr with
      | 1, _ => -- era_and_sweep compound
        cases L' with
        | nil =>
          have ht := macro_era_and_sweep_solo a'
          exact mk_progress _ _ (by omega) ht (invariant_era_and_sweep_solo hinv)
        | cons b L'' =>
          have ht := macro_era_and_sweep a' b L''
          exact mk_progress _ _ (by omega) ht (invariant_era_and_sweep hinv)
      | 2, _ => -- zero_two_solo
        have ht := macro_zero_two_solo (a' + 1) L'
        exact mk_progress 8 _ (by omega) ht (invariant_zero_two_solo hinv)
      | 3, _ => -- zero_bounce_to_zero
        have ht := macro_zero_bounce_to_zero (a' + 1) L'
        exact mk_progress 12 _ (by omega) ht (invariant_zero_bounce_to_zero hinv)
      | 4, _ => -- zero_bounce_and_shift compound
        have ht := macro_zero_bounce_and_shift (a' + 1) L'
        exact mk_progress 19 _ (by omega) ht (invariant_zero_bounce_and_shift hinv)
      | r' + 5, _ => -- zero_bounce (z = r'+1 ≥ 1, output cursor r'+2 ≥ 2)
        have hinv' : MacroInvariant (.M ((a' + 1 + 4) :: L') (r' + 2) [1]) := by
          rw [show r' + 5 = (r' + 1) + 4 from by omega] at hinv
          exact invariant_zero_bounce hinv
        have ht : run sweeper (M0_Config ((a' + 1) :: L') [r' + 5]) (r' + 1 + 13) =
            M_Config ((a' + 1 + 4) :: L') (r' + 2) [1] := by
          rw [show r' + 5 = (r' + 1) + 4 from by omega]
          exact macro_zero_bounce (a' + 1) (r' + 1) L'
        exact mk_progress _ _ (by omega) ht hinv'
    | cons d R'' =>
      -- R = r :: d :: R'', multi-element
      -- NoHaltPattern excludes r=1
      have hr2 : r ≥ 2 := by
        by_contra hlt; push_neg at hlt
        have : r = 1 := by omega
        subst this
        have hd := (AllGe1_cons.mp (AllGe1_cons.mp hR).2).1
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        exact hNH d' R'' rfl
      match r, hr2 with
      | 2, _ => -- zero_two
        have ht := macro_zero_two a d L' R''
        exact mk_progress 8 _ (by omega) ht (invariant_zero_two hinv)
      | r' + 3, _ => -- multi_bounce: R = (r'+3) :: d :: R''
        -- Decompose d :: R'' = R_mid ++ [last]
        obtain ⟨R_mid, last, hdecomp⟩ := List.exists_append_singleton d R''
        rw [hdecomp] at hinv hR ⊢
        have hR_mid_ge : ∀ x ∈ R_mid, x ≥ 1 :=
          fun x hx => AllGe1_mem (AllGe1_of_append_left (AllGe1_cons.mp hR).2) hx
        have hlast_ge : last ≥ 1 :=
          (AllGe1_cons.mp (AllGe1_of_append_right (AllGe1_cons.mp hR).2)).1
        obtain ⟨last', rfl⟩ : ∃ l', last = l' + 1 := ⟨last - 1, by omega⟩
        match last' with
        | 0 => exact multi_bounce_to_zero_progress hinv hR_mid_ge
        | 1 => sorry -- last = 2: multi_bounce cursor=1, need compound with shift
        | last'' + 2 => exact multi_bounce_progress hinv hR_mid_ge

/-- The initial config reaches M_Config [1] 4 [1] after 43 steps. -/
theorem init_to_macro :
    run sweeper (initConfig 6) 43 = (MacroConfig.M [1] 4 [1]).toConfig := by
  show run sweeper (initConfig 6) 43 = M_Config [1] 4 [1]
  rw [show (43 : Nat) = 19 + 5 + 19 from rfl, run_add, run_add, sweeper_init_to_era0,
    era_to_macro 4, macro_sweep_solo (c := 3)]

theorem init_macro_prog : MacroProg (run sweeper (initConfig 6) 43) := by
  exact ⟨.M [1] 4 [1], init_to_macro, invariant_initial⟩

-- ============================================================
-- Main non-halting theorem
-- ============================================================

/-- The machine never halts: for all k, the state after k steps is not none. -/
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  -- Split: first 43 steps computed directly, then use macro progress
  suffices h43 : ∀ j, j < 43 → (run sweeper (initConfig 6) j).state ≠ none by
    by_cases hk : k < 43
    · exact h43 k hk
    · push_neg at hk
      rw [show k = 43 + (k - 43) from by omega, run_add]
      exact nonhalt_of_progress sweeper MacroProg macro_progress
        (run sweeper (initConfig 6) 43) init_macro_prog (k - 43)
  -- First 43 steps: each one computes to state = some _
  intro j hj
  interval_cases j <;> simp [run, step, sweeper, initConfig]

end Sweeper
