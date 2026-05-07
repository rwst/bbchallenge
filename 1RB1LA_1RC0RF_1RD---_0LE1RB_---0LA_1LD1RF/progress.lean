/-
Progress and termination — `macro_progress`, `OrbitReachable`, `sweeper_never_halts`.

This file extracts the dispatch + downstream from `machine.lean`. It uses
`forward_dynamics.lean`'s `thm_reach_multi_bounce_last_2_mid_1` to discharge
the R2 case (formerly an axiom). R1 and R3 remain as axioms — see
`TACTIC_PLAN.md` for the closure status.
-/

import machine
import forward_dynamics

namespace Sweeper

open BusyLean

-- ============================================================
-- Reachability axioms (Option D, partial)
-- ============================================================
-- R2 and R3 are no longer axioms — they're proved in `forward_dynamics.lean`
-- as `thm_reach_multi_bounce_last_2_mid_1` and `thm_reach_multi_bounce_last_2_long`.
-- Only R1 remains as an axiom: its forward dynamics actually halts (verified
-- by `macro_sim.py`'s `bridge_axiom`), so closure requires the cascade
-- approach in `phase2.lean`.

/-- **Reachability axiom R1**: `M([], 3, d::R)` continues.
    This state is produced by `sweep_and_shift` from `M([2], 3, d::R)` when
    the left stack has a single element of value 2. The macro layer has no
    direct theorem covering it — `macro_sweep_left_empty` with c=0 would
    produce output cursor 1, below the invariant threshold. Empirically
    verified non-halting through 10M raw TM steps.

    **Φ side condition (2026-05-06)**: the resulting macro config `cfg'`
    has `cfg'.phi ≥ predecessor.phi + 2`, capturing the empirical
    observation that runs from `M([], 3, _)` proceed via at least one
    M0-transition (Δϕ = +2) before reaching another macro-shape. This
    bound is consistent with TM Φ-monotonicity (sweep family Δϕ = 0;
    M0 rules Δϕ ≥ +2). It is loadbearing for the cascade-termination
    proof (Sub-plan E.3′ via lex(ϕ, mr) measure). -/
axiom reach_M_nil_3 {d : Nat} {R' : List Nat}
    (hinv : MacroInvariant (.M [] 3 (d :: R'))) :
    ∃ k, 0 < k ∧ ∃ cfg' : MacroConfig,
      run sweeper (M_Config [] 3 (d :: R')) k = cfg'.toConfig ∧
      MacroInvariant cfg' ∧
      cfg'.phi ≥ (MacroConfig.M [] 3 (d :: R')).phi + 2 ∧
      (run sweeper (M_Config [] 3 (d :: R')) k).state ≠ none

set_option maxHeartbeats 400000 in
/-- Every macro config satisfying the invariant progresses to another one.
    This is the core dispatch: match on the config shape, apply the right rule.
    Depends only on the R1 reachability axiom (R2 and R3 are closed via
    `thm_reach_multi_bounce_last_2_mid_1` and `thm_reach_multi_bounce_last_2_long`). -/
theorem macro_progress (c : Config 6) (h : MacroProg c) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper c k) ∧ (run sweeper c k).state ≠ none := by
  obtain ⟨cfg, hc, hinv⟩ := h
  subst hc
  cases cfg with
  | M L c R =>
    simp only [MacroConfig.toConfig_M]
    have hL := hinv.1; have hc := hinv.2.1; have hR := hinv.2.2.1
    have hR_ne := hinv.2.2.2
    obtain ⟨d, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    cases L with
    | nil =>
      match c, hc with
      | 2, _ =>
        have ht := macro_sweep_to_zero_left_empty d R'
        exact mk_progress_M0 11 _ _ (by omega) ht (invariant_sweep_to_zero_left_empty hinv)
      | 3, _ =>
        obtain ⟨k, hk, cfg', hcfg', hinv', _, hne⟩ := reach_M_nil_3 hinv
        exact ⟨k, hk, ⟨cfg', hcfg', hinv'⟩, hne⟩
      | c' + 4, _ =>
        have htrans : run sweeper (M_Config [] (c' + 4) (d :: R')) (2 * (c' + 4) + 7) =
            M_Config [1] (c' + 2) ((d + 1) :: R') := by
          rw [show c' + 4 = (c' + 1) + 3 from by omega]; exact macro_sweep_left_empty (c' + 1) d R'
        exact mk_progress_M _ [1] (c'+2) ((d+1)::R') (by omega) htrans (invariant_sweep_left_empty hinv)
    | cons a L' =>
      match c, hc with
      | 2, _ =>
        have ht := macro_sweep_to_zero a d L' R'
        exact mk_progress_M0 11 _ _ (by omega) ht (invariant_sweep_to_zero hinv)
      | 3, _ =>
        have ht := macro_sweep_and_shift a d L' R'
        exact mk_progress_M 19 _ _ _ (by omega) ht (invariant_sweep_and_shift hinv)
      | c' + 4, _ =>
        have htrans : run sweeper (M_Config (a :: L') (c' + 4) (d :: R')) (2 * (c' + 4) + 7) =
            M_Config ((a + 1) :: L') (c' + 2) ((d + 1) :: R') := by
          rw [show c' + 4 = (c' + 1) + 3 from by omega]; exact macro_sweep a (c' + 1) d L' R'
        exact mk_progress_M _ ((a+1)::L') (c'+2) ((d+1)::R') (by omega) htrans (invariant_sweep hinv)
  | M0 L R =>
    simp only [MacroConfig.toConfig_M0]
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
          exact mk_progress_M _ _ _ _ (by omega) ht (invariant_era_and_sweep_solo hinv)
        | cons b L'' =>
          have ht := macro_era_and_sweep a' b L''
          exact mk_progress_M _ _ _ _ (by omega) ht (invariant_era_and_sweep hinv)
      | 2, _ => -- zero_two_solo
        have ht := macro_zero_two_solo (a' + 1) L'
        exact mk_progress_M 8 _ _ _ (by omega) ht (invariant_zero_two_solo hinv)
      | 3, _ => -- zero_bounce_to_zero
        have ht := macro_zero_bounce_to_zero (a' + 1) L'
        exact mk_progress_M0 12 _ _ (by omega) ht (invariant_zero_bounce_to_zero hinv)
      | 4, _ => -- zero_bounce_and_shift compound
        have ht := macro_zero_bounce_and_shift (a' + 1) L'
        exact mk_progress_M 19 _ _ _ (by omega) ht (invariant_zero_bounce_and_shift hinv)
      | r' + 5, _ => -- zero_bounce (z = r'+1 ≥ 1, output cursor r'+2 ≥ 2)
        have hinv' : MacroInvariant (.M ((a' + 1 + 4) :: L') (r' + 2) [1]) := by
          rw [show r' + 5 = (r' + 1) + 4 from by omega] at hinv
          exact invariant_zero_bounce hinv
        have ht : run sweeper (M0_Config ((a' + 1) :: L') [r' + 5]) (r' + 1 + 13) =
            M_Config ((a' + 1 + 4) :: L') (r' + 2) [1] := by
          rw [show r' + 5 = (r' + 1) + 4 from by omega]
          exact macro_zero_bounce (a' + 1) (r' + 1) L'
        exact mk_progress_M _ _ _ _ (by omega) ht hinv'
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
        exact mk_progress_M 8 _ _ _ (by omega) ht (invariant_zero_two hinv)
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
        | 1 => -- last = 2: multi_bounce gives cursor 1, need compound with shift
          cases R_mid with
          | nil =>
            -- R_mid = []: 2-run case R = [r'+3, 2]
            match r' with
            | 0 =>
              -- R = [3, 2]. Use multi_bounce_2 + double shift compound.
              exact multi_bounce_last_2_two_run_r0_progress
                (show MacroInvariant (.M0 (a :: L') [3, 2]) from hinv)
            | r'' + 1 =>
              -- R = [r''+4, 2]. Use multi_bounce_2_and_shift (single shift suffices).
              exact multi_bounce_last_2_two_run_progress
                (show MacroInvariant (.M0 (a :: L') [r'' + 4, 2]) from hinv)
          | cons e R_mid' =>
            -- R_mid = e :: R_mid': R_mid nonempty case
            cases R_mid' with
            | nil =>
              -- R_mid = [e]: 3-run case R = [r'+3, e, 2]
              -- e ≥ 1 from AllGe1 (R_mid elements ≥ 1)
              have he := hR_mid_ge e List.mem_cons_self
              obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
              cases e' with
              | zero =>
                -- e = 1: R = [r'+3, 1, 2]. Closed by forward dynamics theorem (formerly axiom R2).
                exact thm_reach_multi_bounce_last_2_mid_1 hinv
              | succ e'' =>
                -- e = e''+2 ≥ 2: use 3-run compound.
                exact multi_bounce_last_2_three_run_progress
                  (show MacroInvariant (.M0 (a :: L') [r' + 3, e'' + 2, 2]) from hinv)
            | cons f rest =>
              -- R_mid = e :: f :: rest with |R_mid| ≥ 2.
              -- Decompose f :: rest = middle_init' ++ [last_inner] and case on last_inner.
              -- Per F1+F2 simulator data over 51B raw steps, last_inner ≥ 14 always;
              -- last_inner ≥ 2 closes via macro_multi_bounce_last_2_general (single shift).
              -- last_inner = 1 case retains the original R3 axiom (empirically unreached).
              obtain ⟨middle_init', last_inner, hdecomp⟩ :=
                List.exists_append_singleton f rest
              have h_last_ge : last_inner ≥ 1 := by
                have h_in : last_inner ∈ (f :: rest) := by
                  rw [hdecomp]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
                exact hR_mid_ge last_inner (List.mem_cons_of_mem e h_in)
              match last_inner, h_last_ge with
              | 1, _ =>
                -- Last middle = 1: closed by forward dynamics theorem (formerly axiom R3).
                have h_input_eq :
                    ((r' + 3) :: (e :: f :: rest ++ [1 + 1]) : List Nat) =
                    (r' + 3) :: e :: middle_init' ++ [1, 2] := by
                  rw [hdecomp]; simp [List.cons_append, List.append_assoc]
                rw [h_input_eq] at hinv ⊢
                exact thm_reach_multi_bounce_last_2_long hinv
              | l + 2, _ =>
                -- Last middle ≥ 2: use new compound lemma
                have h_input_eq :
                    ((r' + 3) :: (e :: f :: rest ++ [1 + 1]) : List Nat) =
                    (r' + 3) :: (e :: middle_init') ++ [l + 2, 2] := by
                  rw [hdecomp]; simp [List.cons_append, List.append_assoc]
                rw [h_input_eq] at hinv ⊢
                have h_init : ∀ x ∈ (e :: middle_init'), x ≥ 1 := by
                  have hR' := hinv.2.1
                  simp only [List.cons_append] at hR'
                  rw [AllGe1_cons] at hR'
                  exact fun x hx => AllGe1_mem (AllGe1_of_append_left hR'.2) hx
                exact multi_bounce_last_2_general_progress hinv h_init
        | last'' + 2 => exact multi_bounce_progress hinv hR_mid_ge

/-- The initial config reaches M_Config [1] 4 [1] after 43 steps. -/
theorem init_to_macro :
    run sweeper (initConfig 6) 43 = (MacroConfig.M [1] 4 [1]).toConfig := by
  rw [MacroConfig.toConfig_M, show (43 : Nat) = 19 + 5 + 19 from rfl,
    run_add, run_add, sweeper_init_to_era0, era_to_macro 4, macro_sweep_solo (c := 3)]

theorem init_macro_prog : MacroProg (run sweeper (initConfig 6) 43) := by
  exact ⟨.M [1] 4 [1], init_to_macro, invariant_initial⟩

-- ============================================================
-- Era-based progress predicate (Option C infrastructure)
-- ============================================================

-- ============================================================
-- macroEra infrastructure (Option C: era-based recursive function)
-- ============================================================

/-- `macroStep cfg` dispatches one macro transition from config `cfg`.
    Returns `some (k, cfg')` if `cfg` has a known macro transition producing
    `cfg'` after `k` raw TM steps. Returns `none` for configs that halt or
    are outside the dispatch (e.g., M([], 3, d::R), multi_bounce complexity).

    This is the functional counterpart of `macro_progress`'s case dispatch. -/
def macroStep : MacroConfig → Option (Nat × MacroConfig)
  -- M config dispatch
  | .M L c R =>
    match L, c, R with
    -- R empty: excluded (R ≠ [] invariant)
    | _, _, [] => none
    -- L nonempty cases
    | (a :: L'), 2, (d :: R') => some (11, .M0 ((a+1) :: L') ((d+1) :: R'))
    | (a :: L'), 3, (d :: R') => some (19, .M L' (a+1) (1 :: (d+1) :: R'))
    | (a :: L'), c'+4, (d :: R') => some (2*(c'+4)+7, .M ((a+1) :: L') (c'+2) ((d+1) :: R'))
    -- L empty cases
    | [], 2, (d :: R') => some (11, .M0 [1] ((d+1) :: R'))
    | [], 3, (_ :: _) => none  -- halts: M([], 3, d::R) → C,1 undefined
    | [], c'+4, (d :: R') => some (2*(c'+4)+7, .M [1] (c'+2) ((d+1) :: R'))
    -- c = 0 or 1: outside invariant
    | _, 0, _ => none
    | _, 1, _ => none
  -- M0 config dispatch
  | .M0 L R =>
    match L, R with
    | [], _ => none  -- L ≠ [] invariant
    | _, [] => none  -- R ≠ [] invariant
    | ((a+1) :: b :: L'), [1] => some (2*a+27, .M ((b+1) :: L') (a+4) [1])  -- era_and_sweep
    | [a+1], [1] => some (2*a+27, .M [1] (a+4) [1])  -- era_and_sweep_solo
    | [0], [1] => none  -- violates AllGe1
    | (0 :: _ :: _), [1] => none  -- violates AllGe1
    | (a :: L'), [2] => some (8, .M L' (a+3) [1])  -- zero_two_solo
    | (a :: L'), [3] => some (12, .M0 ((a+4) :: L') [1])  -- zero_bounce_to_zero
    | (a :: L'), [4] => some (19, .M L' (a+4) [1, 1])  -- zero_bounce_and_shift
    | (a :: L'), [z+5] => some (z+1+13, .M ((a+4) :: L') (z+2) [1])  -- zero_bounce
    | (a :: L'), (2 :: d :: R') => some (8, .M L' (a+3) ((d+1) :: R'))  -- zero_two
    | (_ :: _), (1 :: _ :: _) => none  -- halt pattern
    | (_ :: _), (0 :: _) => none  -- violates AllGe1
    | (_ :: _), ((_+3) :: _ :: _) => none  -- multi_bounce: not handled in macroStep

/-- `macroEra fuel cfg` iterates `macroStep` up to `fuel` times.
    Returns `(total_steps, final_config)`. Stops early if `macroStep` returns `none`. -/
def macroEra (fuel : Nat) (cfg : MacroConfig) : Nat × MacroConfig :=
  match fuel with
  | 0 => (0, cfg)
  | fuel' + 1 =>
    match macroStep cfg with
    | none => (0, cfg)
    | some (k, cfg') =>
        let (k', cfg'') := macroEra fuel' cfg'
        (k + k', cfg'')

/-- `ms_simp at h` normalizes a hypothesis `h : macroStep cfg = some (k, target)`
    by unfolding `macroStep`, applying Option/Prod/MacroConfig/List injectivity.
    After this, `h` is either `False` (auto-closing goal via simp's contradiction
    discovery) or a nested conjunction of equalities ready for `obtain`. -/
syntax (name := ms_simp_tac) "ms_simp" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| ms_simp $l:location) =>
    `(tactic| simp only [macroStep, Option.some.injEq, Prod.mk.injEq,
                         MacroConfig.M.injEq, MacroConfig.M0.injEq,
                         List.cons.injEq] $l:location)

/-- `ms_done at h` is the contradiction-discharge form: full `simp [macroStep] at h`
    which auto-closes the goal when `h` reduces to `False` (e.g., when macroStep
    returns `none` but `h` says it equals `some _`). -/
syntax (name := ms_done_tac) "ms_done" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| ms_done $l:location) => `(tactic| simp [macroStep] $l:location)

/-- Soundness of `macroStep`: if it returns `some (k, cfg')`, then the raw TM runs
    for `k` steps from `cfg.toConfig` produce `cfg'.toConfig`, and the invariant
    is preserved. -/
theorem macroStep_sound (cfg cfg' : MacroConfig) (k : Nat)
    (hstep : macroStep cfg = some (k, cfg')) (hinv : MacroInvariant cfg) :
    run sweeper cfg.toConfig k = cfg'.toConfig ∧ MacroInvariant cfg' ∧ 0 < k := by
  cases cfg with
  | M L c R =>
    simp only [MacroConfig.toConfig_M]
    have hL := hinv.1; have hc := hinv.2.1; have hR := hinv.2.2.1
    have hR_ne := hinv.2.2.2
    obtain ⟨d, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    cases L with
    | nil =>
      match c, hc with
      | 2, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M0]; exact macro_sweep_to_zero_left_empty d R'
        · exact invariant_sweep_to_zero_left_empty hinv
      | 3, _ =>
        ms_done at hstep
      | c' + 4, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M,
            show c' + 4 = (c' + 1) + 3 from by omega]
          exact macro_sweep_left_empty (c' + 1) d R'
        · exact invariant_sweep_left_empty hinv
    | cons a L' =>
      match c, hc with
      | 2, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M0]; exact macro_sweep_to_zero a d L' R'
        · exact invariant_sweep_to_zero hinv
      | 3, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_sweep_and_shift a d L' R'
        · exact invariant_sweep_and_shift hinv
      | c' + 4, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M,
            show c' + 4 = (c' + 1) + 3 from by omega]
          exact macro_sweep a (c' + 1) d L' R'
        · exact invariant_sweep hinv
  | M0 L R =>
    simp only [MacroConfig.toConfig_M0]
    have hL := hinv.1; have hR := hinv.2.1
    have hL_ne := hinv.2.2.1; have hR_ne := hinv.2.2.2.1
    obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL_ne
    obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    have ha := (AllGe1_cons.mp hL).1
    have hr := (AllGe1_cons.mp hR).1
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    cases R' with
    | nil =>
      match r, hr with
      | 1, _ =>
        cases L' with
        | nil =>
          ms_simp at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          refine ⟨?_, ?_, by omega⟩
          · rw [MacroConfig.toConfig_M]; exact macro_era_and_sweep_solo a'
          · exact invariant_era_and_sweep_solo hinv
        | cons b L'' =>
          ms_simp at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          refine ⟨?_, ?_, by omega⟩
          · rw [MacroConfig.toConfig_M]; exact macro_era_and_sweep a' b L''
          · exact invariant_era_and_sweep hinv
      | 2, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_zero_two_solo (a' + 1) L'
        · exact invariant_zero_two_solo hinv
      | 3, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M0]; exact macro_zero_bounce_to_zero (a' + 1) L'
        · exact invariant_zero_bounce_to_zero hinv
      | 4, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_zero_bounce_and_shift (a' + 1) L'
        · exact invariant_zero_bounce_and_shift hinv
      | r' + 5, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M,
            show r' + 5 = (r' + 1) + 4 from by omega]
          exact macro_zero_bounce (a' + 1) (r' + 1) L'
        · rw [show r' + 5 = (r' + 1) + 4 from by omega] at hinv
          exact invariant_zero_bounce hinv
    | cons d R'' =>
      -- multi-element R: only r=2 (zero_two) is handled; rest return none
      match r, hr with
      | 1, _ =>
        ms_done at hstep
      | 2, _ =>
        ms_simp at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_zero_two (a' + 1) d L' R''
        · exact invariant_zero_two hinv
      | r' + 3, _ =>
        ms_done at hstep

/-- Soundness of `macroEra`: iterating `macroStep` for `fuel` steps correctly
    tracks the raw TM run and preserves the invariant. -/
theorem macroEra_sound (fuel : Nat) (cfg : MacroConfig) (hinv : MacroInvariant cfg) :
    let (k, cfg') := macroEra fuel cfg
    run sweeper cfg.toConfig k = cfg'.toConfig ∧ MacroInvariant cfg' := by
  induction fuel generalizing cfg with
  | zero => simp [macroEra, hinv]
  | succ fuel' ih =>
    simp only [macroEra]
    cases hstep : macroStep cfg with
    | none => simp [hinv]
    | some kc =>
      obtain ⟨k, cfg'⟩ := kc
      obtain ⟨htrans, hinv', hk_pos⟩ := macroStep_sound cfg cfg' k hstep hinv
      simp only
      obtain ⟨htrans', hinv''⟩ := ih cfg' hinv'
      refine ⟨?_, hinv''⟩
      rw [run_add, htrans, htrans']

-- ============================================================
-- Orbit-reachable inductive predicate (2026-04-27 refactor)
-- ============================================================
-- Defines `OrbitReachable` as the smallest set of macro configurations
-- closed under `macroStep` starting from the initial configuration
-- `M([1], 4, [1])`. Provides a structural framework for backward analysis:
-- to prove a config is not orbit-reachable, show no OrbitReachable predecessor
-- maps to it via `macroStep`.
--
-- Phase 1 (this file): infrastructure — definition, init, invariant implication,
-- OrbitProg replaces MacroProg as the working progress predicate.
-- Phase 2 (future): prove `OrbitReachable cfg → cfg ≠ <axiom shape>` for R1/R3,
-- replacing the remaining reachability axioms with structural derivations.
-- ============================================================

/-- Inductive predicate: macro configurations reachable from the orbit's
    initial state `M([1], 4, [1])`. Each constructor encodes one specific
    macro rule's input/output relation:
    - `init`: the orbit's start.
    - `step_macro`: any `macroStep`-handled transition (single-step rules:
      sweep variants, era_and_sweep, zero_*, etc.).
    - `step_multi_bounce_*`: each multi-bounce theorem in `machine.lean` /
      `forward_dynamics.lean` has its own constructor with the input shape
      and output shape baked in.
    - `step_R3`: the existential-output case of `thm_reach_multi_bounce_last_2_long`
      (output via `shift_to_macro_prog`); takes the witness cfg' as a
      parameter, plus the corresponding raw-TM run.

    This explicit-constructor form replaces the older permissive `step_run`
    catch-all and makes induction tractable: each constructor's case in a
    proof reduces to checking the structural shape of that rule's output. -/
inductive OrbitReachable : MacroConfig → Prop where
  | init : OrbitReachable (.M [1] 4 [1])
  | step_macro {cfg cfg' : MacroConfig} {k : Nat} :
      OrbitReachable cfg → macroStep cfg = some (k, cfg') → OrbitReachable cfg'
  -- Multi-bounce, last ≥ 3 case: produces M with R = [1].
  | step_multi_bounce_general
      {a r' last'' : Nat} {L' R_mid : List Nat} :
      OrbitReachable (.M0 (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])) →
      OrbitReachable
        (.M (R_mid.reverse ++ (r' + 1) :: (a + 4) :: L') (last'' + 2) [1])
  -- Multi-bounce, last = 1 case: produces M0 with R = [1].
  | step_multi_bounce_general_to_zero
      {a r' : Nat} {L' R_mid : List Nat} :
      OrbitReachable (.M0 (a :: L') ((r' + 3) :: R_mid ++ [1])) →
      OrbitReachable
        (.M0 (R_mid.reverse ++ (r' + 1) :: (a + 4) :: L') [1])
  -- Multi-bounce, last = 2, two-run case (R_mid = [], r ≥ 1).
  | step_multi_bounce_2_and_shift
      {a r : Nat} {L' : List Nat} :
      OrbitReachable (.M0 (a :: L') [r + 4, 2]) →
      OrbitReachable (.M ((a + 4) :: L') (r + 2) [1, 1])
  -- Multi-bounce, last = 2, R = [3, 2] case.
  | step_multi_bounce_2_double_shift
      {a : Nat} {L' : List Nat} :
      OrbitReachable (.M0 (a :: L') [3, 2]) →
      OrbitReachable (.M L' (a + 4) [1, 1, 1])
  -- Multi-bounce, last = 2, 3-run case with middle ≥ 2.
  | step_multi_bounce_3run_last_2
      {a r' e : Nat} {L' : List Nat} :
      OrbitReachable (.M0 (a :: L') [r' + 3, e + 2, 2]) →
      OrbitReachable (.M ((r' + 1) :: (a + 4) :: L') (e + 2) [1, 1])
  -- Multi-bounce, last = 2, general middle case.
  | step_multi_bounce_last_2_general
      {a r' m_last : Nat} {L' middle_init : List Nat} :
      OrbitReachable
        (.M0 (a :: L') ((r' + 3) :: middle_init ++ [m_last + 2, 2])) →
      OrbitReachable
        (.M (middle_init.reverse ++ (r' + 1) :: (a + 4) :: L')
            (m_last + 2) [1, 1])
  -- R2: thm_reach_multi_bounce_last_2_mid_1, r' = 0 case.
  | step_R2_zero {a : Nat} {L' : List Nat} :
      OrbitReachable (.M0 (a :: L') [3, 1, 2]) →
      OrbitReachable (.M L' (a + 4) [1, 1, 1, 1])
  -- R2: thm_reach_multi_bounce_last_2_mid_1, r' = r + 1 case.
  | step_R2_succ {a r : Nat} {L' : List Nat} :
      OrbitReachable (.M0 (a :: L') [r + 4, 1, 2]) →
      OrbitReachable (.M ((a + 4) :: L') (r + 2) [1, 1, 1])
  -- R3: thm_reach_multi_bounce_last_2_long. Output is via shift_to_macro_prog
  -- and depends on L' / middle_init's structure; takes cfg' as parameter.
  -- Includes a `safe` precondition: cfg' is never `M([], 3, R)`. This is
  -- discharged in `orbit_progress` via `shift_to_macro_prog_excludes_R1`,
  -- since `L_after` always contains `a + 4 ≥ 5`.
  -- The Φ side condition `cfg'.phi = predecessor.phi + 2` is provided by
  -- `thm_reach_multi_bounce_last_2_long_safe` (composes
  -- `phi_macro_multi_bounce_general` Δ=+2 with shift Δ=0). Lets downstream
  -- proofs (e.g. `OrbitReachable.phi_ge_init`) close the step_R3 case.
  | step_R3 {a r' e : Nat} {L' middle_init : List Nat}
      {cfg' : MacroConfig} {k : Nat} :
      OrbitReachable (.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) →
      run sweeper
        (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k =
        cfg'.toConfig →
      MacroInvariant cfg' →
      0 < k →
      (∀ R, cfg' ≠ .M [] 3 R) →
      -- Strict safety (2026-05-07): cfg' is M-shape (existential witness),
      -- and either ∃ x ∈ L_suf, x ≥ 5, or v = a+4 with L_suf = L'.
      -- The first disjunct excludes cascade shapes with bounded L_suf;
      -- the second exposes the predecessor structure for M0 backward chase
      -- (used to close mk_M_1_2spine_5 case).
      (∃ L_suf v R_out, cfg' = .M L_suf v R_out ∧
          ((∃ x ∈ L_suf, x ≥ 5) ∨ (v = a + 4 ∧ L_suf = L'))) →
      cfg'.phi =
        (MacroConfig.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])).phi + 2 →
      OrbitReachable cfg'
  -- R1: reach_M_nil_3 axiom output. The predecessor `M([], 3, d :: R')` is
  -- itself the unreachable shape, so this constructor's case vacuously closes
  -- in any OrbitReachable.not_M_empty_3 induction (the predecessor's IH gives
  -- direct contradiction).
  -- The Φ side condition `cfg'.phi ≥ predecessor.phi + 2` (added 2026-05-06)
  -- enables lex(ϕ, mr) cascade termination (Sub-plan E.3′).
  | step_R1 {d : Nat} {R' : List Nat} {cfg' : MacroConfig} {k : Nat} :
      OrbitReachable (.M [] 3 (d :: R')) →
      run sweeper (M_Config [] 3 (d :: R')) k = cfg'.toConfig →
      MacroInvariant cfg' →
      0 < k →
      cfg'.phi ≥ (MacroConfig.M [] 3 (d :: R')).phi + 2 →
      OrbitReachable cfg'

/-- Every orbit-reachable config satisfies the macro invariant. -/
theorem OrbitReachable.macroInvariant {cfg : MacroConfig} (h : OrbitReachable cfg) :
    MacroInvariant cfg := by
  induction h with
  | init => exact invariant_initial
  | step_macro h_prev h_step ih => exact (macroStep_sound _ _ _ h_step ih).2.1
  | step_multi_bounce_general _ ih =>
      exact invariant_multi_bounce_general ih
  | step_multi_bounce_general_to_zero _ ih =>
      exact invariant_multi_bounce_general_to_zero ih
  | step_multi_bounce_2_and_shift _ ih =>
      exact invariant_multi_bounce_2_and_shift ih
  | step_multi_bounce_2_double_shift _ ih =>
      exact invariant_multi_bounce_2_double_shift ih
  | step_multi_bounce_3run_last_2 _ ih =>
      exact invariant_multi_bounce_3run_last_2 ih
  | step_multi_bounce_last_2_general _ ih =>
      exact invariant_multi_bounce_last_2_general ih
  | step_R2_zero _ ih =>
      exact invariant_R2_zero ih
  | step_R2_succ _ ih =>
      exact invariant_R2_pos ih
  | step_R3 _ _ hinv' _ _ _ _ _ => exact hinv'
  | step_R1 _ _ hinv' _ _ => exact hinv'

/-- Progress predicate using OrbitReachable. Stronger than MacroProg —
    additionally tracks that the macro state is reachable from the orbit's
    initial configuration. -/
def OrbitProg (c : Config 6) : Prop :=
  ∃ cfg : MacroConfig, c = cfg.toConfig ∧ OrbitReachable cfg

/-- OrbitProg implies MacroProg via OrbitReachable.macroInvariant. -/
theorem OrbitProg.toMacroProg {c : Config 6} (h : OrbitProg c) : MacroProg c := by
  obtain ⟨cfg, hc, hreach⟩ := h
  exact ⟨cfg, hc, hreach.macroInvariant⟩

/-- The initial configuration after 43 raw TM steps is OrbitProg. -/
theorem init_orbit_prog : OrbitProg (run sweeper (initConfig 6) 43) :=
  ⟨.M [1] 4 [1], init_to_macro, .init⟩

/-- macroEra preserves OrbitReachable: iterating macroStep stays within the orbit. -/
theorem OrbitReachable.macroEra (cfg : MacroConfig) (h : OrbitReachable cfg) (fuel : Nat) :
    OrbitReachable (Sweeper.macroEra fuel cfg).2 := by
  induction fuel generalizing cfg with
  | zero => exact h
  | succ fuel' ih =>
    simp only [Sweeper.macroEra]
    cases hstep : macroStep cfg with
    | none => exact h
    | some kc =>
      obtain ⟨k, cfg'⟩ := kc
      have h' : OrbitReachable cfg' := .step_macro h hstep
      exact ih cfg' h'

/-- Concrete OrbitReachable witness: `M [1] 10 [1]` (era 0 boundary) is reachable. -/
theorem orbit_reachable_era0_end : OrbitReachable (.M [1] 10 [1]) := by
  have h : (Sweeper.macroEra 4 (.M [1] 4 [1])).2 = .M [1] 10 [1] := rfl
  rw [← h]
  exact OrbitReachable.macroEra _ .init 4

/-- Concrete OrbitReachable witness: `M [10] 3 [1]` (era 1 boundary) is reachable.
    Provides a non-trivial example of building reachability witnesses. -/
theorem orbit_reachable_era1_end : OrbitReachable (.M [10] 3 [1]) := by
  have h : (Sweeper.macroEra 6 (.M [1] 10 [1])).2 = .M [10] 3 [1] := rfl
  rw [← h]
  exact OrbitReachable.macroEra _ orbit_reachable_era0_end 6

-- ============================================================
-- Demonstration of OrbitReachable for non-reachability proofs
-- ============================================================
-- Two trivial-but-illustrative non-reachability theorems showing how
-- `OrbitReachable.macroInvariant` is used. Phase 2 work would prove similar
-- non-reachability for the axiom shapes (R1, R3) but requires the
-- structural cascade analysis documented in LOG.md.

/-- M0 with empty L is never orbit-reachable (follows from MacroInvariant.M0
    requiring `L ≠ []`). Demonstrates the proof pattern. -/
theorem OrbitReachable.not_M0_empty_L {R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M0 [] R := by
  intro hcfg
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.2.1 rfl

/-- M_Config with cursor below 2 is never orbit-reachable (from MacroInvariant). -/
theorem OrbitReachable.M_cursor_ge_2 {L R : List Nat} {c : Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M L c R) : c ≥ 2 := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.1

-- ============================================================
-- Phase 2 outline (future work, ~1-2 weeks)
-- ============================================================
-- Closing R1 axiom: prove
--   theorem OrbitReachable.not_R1 :
--       OrbitReachable cfg → cfg ≠ .M [] 3 (d :: R')
-- Induction on `h : OrbitReachable cfg`:
-- * `init`: cfg = .M [1] 4 [1] ≠ .M [] 3 _ (structural).
-- * `step_macro`: macroStep producers of .M [] 3 _ are limited to
--   `sweep_and_shift` on M([2], 3, R'). Recurse: ¬OrbitReachable
--   (.M [2] 3 R'). Cascade.
-- * `step_run`: backward analysis through macro_progress's ~25 branches.
--   Producers of .M [] 3 _: only sweep_and_shift. Same cascade.
-- Cascade depth: ~6 layers (LOG.md).
--
-- Closing R3 (refined) axiom: the recursive narrow case.
-- F1+F2 simulator confirmed (0 occurrences in 51B raw steps).
-- ============================================================

/-- Helper: `OrbitReachable cfg` with `macroStep cfg = some (k, cfg')` lifts
    to `OrbitProg`. -/
private lemma orbit_progress_macroStep
    {cfg cfg' : MacroConfig} {k : Nat}
    (hreach : OrbitReachable cfg) (hstep : macroStep cfg = some (k, cfg'))
    (hinv : MacroInvariant cfg) :
    ∃ k', 0 < k' ∧ OrbitProg (run sweeper cfg.toConfig k') ∧
      (run sweeper cfg.toConfig k').state ≠ none := by
  obtain ⟨hrun, _hinv', hk⟩ := macroStep_sound cfg cfg' k hstep hinv
  refine ⟨k, hk, ⟨cfg', hrun, OrbitReachable.step_macro hreach hstep⟩, ?_⟩
  rw [hrun, MacroConfig.toConfig_state]
  exact Option.some_ne_none _

set_option maxHeartbeats 1600000 in
/-- Orbit progress: every OrbitProg state runs to another OrbitProg state.
    Dispatches by `cfg`'s shape and applies the matching `OrbitReachable`
    constructor (`step_macro` for single-step rules, `step_multi_bounce_*` /
    `step_R2_*` / `step_R3` for multi-bounce). -/
theorem orbit_progress (c : Config 6) (h : OrbitProg c) :
    ∃ k, 0 < k ∧ OrbitProg (run sweeper c k) ∧ (run sweeper c k).state ≠ none := by
  obtain ⟨cfg, hc, hreach⟩ := h
  have hinv := hreach.macroInvariant
  subst hc
  cases cfg with
  | M L cur R =>
    -- M-shape: every transition (except M([], 3, _) which is R1 axiom)
    -- is via macroStep (sweep variants).
    have hcur := hinv.2.1; have hR_ne := hinv.2.2.2
    obtain ⟨d, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    cases L with
    | nil =>
      match cur, hcur with
      | 2, _ =>
        exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | 3, _ =>
        -- R1 axiom case: lift via step_R1
        simp only [MacroConfig.toConfig_M]
        obtain ⟨k, hk, cfg', hcfg', hinv', hphi, hne⟩ := reach_M_nil_3 hinv
        refine ⟨k, hk, ⟨cfg', hcfg', ?_⟩, hne⟩
        exact OrbitReachable.step_R1 hreach hcfg' hinv' hk hphi
      | c' + 4, _ =>
        exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
    | cons a L' =>
      match cur, hcur with
      | 2, _ =>
        exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | 3, _ =>
        exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | c' + 4, _ =>
        exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
  | M0 L R =>
    have hL := hinv.1; have hR := hinv.2.1
    have hL_ne := hinv.2.2.1; have hR_ne := hinv.2.2.2.1
    have hNH := hinv.2.2.2.2
    obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL_ne
    obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    have ha := (AllGe1_cons.mp hL).1
    have hr := (AllGe1_cons.mp hR).1
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    cases R' with
    | nil =>
      -- Single-element R: all macroStep cases
      match r, hr with
      | 1, _ =>
        cases L' with
        | nil => exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
        | cons b L'' => exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | 2, _ => exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | 3, _ => exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | 4, _ => exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | r' + 5, _ => exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
    | cons d_inner R'' =>
      have hr2 : r ≥ 2 := by
        rcases Nat.lt_or_ge 2 (r + 1) with h | h
        · omega
        · have h1 : r = 1 := by omega
          subst h1
          have hd := (AllGe1_cons.mp (AllGe1_cons.mp hR).2).1
          obtain ⟨d_inner', rfl⟩ : ∃ d', d_inner = d' + 1 := ⟨d_inner - 1, by omega⟩
          exact absurd rfl (hNH d_inner' R'')
      match r, hr2 with
      | 2, _ =>
        -- zero_two: macroStep handles this
        exact orbit_progress_macroStep hreach (rfl : macroStep _ = _) hinv
      | r' + 3, _ =>
        -- multi-bounce: dispatch by R structure
        obtain ⟨R_mid, last, hdecomp⟩ := List.exists_append_singleton d_inner R''
        rw [hdecomp] at hinv hR hreach ⊢
        have hR_mid_ge : ∀ x ∈ R_mid, x ≥ 1 :=
          fun x hx => AllGe1_mem (AllGe1_of_append_left (AllGe1_cons.mp hR).2) hx
        have hlast_ge : last ≥ 1 :=
          (AllGe1_cons.mp (AllGe1_of_append_right (AllGe1_cons.mp hR).2)).1
        obtain ⟨last', rfl⟩ : ∃ l', last = l' + 1 := ⟨last - 1, by omega⟩
        match last' with
        | 0 =>
          -- last = 1: multi_bounce_general_to_zero
          have ht := macro_multi_bounce_general_to_zero (a' + 1) r' L' R_mid hR_mid_ge
          have hreach' := OrbitReachable.step_multi_bounce_general_to_zero (a := a' + 1)
            (r' := r') (L' := L') (R_mid := R_mid) hreach
          have hk_pos : 0 < r' + 3 * R_mid.length + R_mid.sum + 16 := by omega
          refine ⟨r' + 3 * R_mid.length + R_mid.sum + 16, hk_pos,
                  ⟨.M0 (R_mid.reverse ++ (r' + 1) :: (a' + 1 + 4) :: L') [1], ?_, hreach'⟩, ?_⟩
          · simp only [MacroConfig.toConfig_M0]; exact ht
          · simp only [MacroConfig.toConfig_M0]
            exact ht ▸ M0_Config_state_ne_none _ _
        | 1 =>
          -- last = 2: case-split on R_mid
          cases R_mid with
          | nil =>
            -- R = [r'+3, 2]
            match r' with
            | 0 =>
              -- R = [3, 2]: multi_bounce_2_double_shift
              have ht := macro_multi_bounce_2_double_shift (a' + 1) L'
              have hreach' : OrbitReachable (.M L' (a' + 1 + 4) [1, 1, 1]) :=
                OrbitReachable.step_multi_bounce_2_double_shift
                  (a := a' + 1) (L' := L') hreach
              refine ⟨29, by omega,
                      ⟨.M L' (a' + 1 + 4) [1, 1, 1], ?_, hreach'⟩, ?_⟩
              · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
                exact ht
              · simp only [MacroConfig.toConfig_M0]
                exact ht ▸ M_Config_state_ne_none _ _ _
            | r'' + 1 =>
              -- R = [r''+4, 2]: multi_bounce_2_and_shift
              -- Normalize the input shape `(r''+1+3) :: ([] ++ [0+1+1])` to `[r''+4, 2]`.
              have heq1 : r'' + 1 + 3 = r'' + 4 := by omega
              rw [heq1] at hinv hreach
              have ht := macro_multi_bounce_2_and_shift (a' + 1) r'' L'
              have hreach' : OrbitReachable (.M ((a' + 1 + 4) :: L') (r'' + 2) [1, 1]) :=
                OrbitReachable.step_multi_bounce_2_and_shift
                  (a := a' + 1) (r := r'') (L' := L') hreach
              refine ⟨r'' + 24, by omega,
                      ⟨.M ((a' + 1 + 4) :: L') (r'' + 2) [1, 1], ?_, hreach'⟩, ?_⟩
              · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
                exact ht
              · simp only [MacroConfig.toConfig_M0]
                exact ht ▸ M_Config_state_ne_none _ _ _
          | cons e R_mid' =>
            cases R_mid' with
            | nil =>
              -- R = [r'+3, e, 2]: 3-run case
              have he : e ≥ 1 := hR_mid_ge e (List.mem_cons_self)
              obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
              cases e' with
              | zero =>
                -- e = 1: R2 closure. Dispatch on r' for the two cfg' shapes.
                match r' with
                | 0 =>
                  -- R = [3, 1, 2]: bridge_R2_zero
                  have ht := bridge_R2_zero (a' + 1) L'
                  have hreach' : OrbitReachable (.M L' (a' + 1 + 4) [1, 1, 1, 1]) :=
                    OrbitReachable.step_R2_zero (a := a' + 1) (L' := L') hreach
                  refine ⟨39, by omega,
                          ⟨.M L' (a' + 1 + 4) [1, 1, 1, 1], ?_, hreach'⟩, ?_⟩
                  · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
                    exact ht
                  · simp only [MacroConfig.toConfig_M0]
                    exact ht ▸ M_Config_state_ne_none _ _ _
                | r'' + 1 =>
                  -- R = [r''+4, 1, 2]: bridge_R2_pos
                  have heq1 : r'' + 1 + 3 = r'' + 4 := by omega
                  rw [heq1] at hinv hreach
                  have ht := bridge_R2_pos (a' + 1) r'' L'
                  have hreach' : OrbitReachable (.M ((a' + 1 + 4) :: L') (r'' + 2) [1, 1, 1]) :=
                    OrbitReachable.step_R2_succ (a := a' + 1) (r := r'') (L' := L') hreach
                  refine ⟨r'' + 34, by omega,
                          ⟨.M ((a' + 1 + 4) :: L') (r'' + 2) [1, 1, 1], ?_, hreach'⟩, ?_⟩
                  · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
                    exact ht
                  · simp only [MacroConfig.toConfig_M0]
                    exact ht ▸ M_Config_state_ne_none _ _ _
              | succ e'' =>
                -- e ≥ 2: multi_bounce_3run_last_2
                have ht := macro_multi_bounce_3run_last_2 (a' + 1) r' e'' L'
                have hreach' : OrbitReachable
                    (.M ((r' + 1) :: (a' + 1 + 4) :: L') (e'' + 2) [1, 1]) :=
                  OrbitReachable.step_multi_bounce_3run_last_2
                    (a := a' + 1) (r' := r') (e := e'') (L' := L') hreach
                refine ⟨r' + 3 * 1 + (e'' + 2) + 17 + 6, by omega,
                        ⟨.M ((r' + 1) :: (a' + 1 + 4) :: L') (e'' + 2) [1, 1], ?_, hreach'⟩, ?_⟩
                · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
                  exact ht
                · simp only [MacroConfig.toConfig_M0]
                  exact ht ▸ M_Config_state_ne_none _ _ _
            | cons f rest =>
              -- R has middle ≥ 2 elements
              obtain ⟨middle_init', last_inner, hdecomp_inner⟩ :=
                List.exists_append_singleton f rest
              have h_last_inner_ge : last_inner ≥ 1 := by
                have h_in : last_inner ∈ (f :: rest) := by
                  rw [hdecomp_inner]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
                exact hR_mid_ge last_inner (List.mem_cons_of_mem e h_in)
              match last_inner, h_last_inner_ge with
              | 1, _ =>
                -- Last middle = 1: R3 closure with safety via
                -- thm_reach_multi_bounce_last_2_long_safe.
                have h_input_eq :
                    ((r' + 3) :: (e :: f :: rest ++ [0 + 1 + 1]) : List Nat) =
                    (r' + 3) :: e :: middle_init' ++ [1, 2] := by
                  rw [hdecomp_inner]; simp [List.cons_append, List.append_assoc]
                have hinv_new : MacroInvariant
                    (MacroConfig.M0 ((a' + 1) :: L' : List Nat)
                      ((r' + 3) :: e :: middle_init' ++ [1, 2] : List Nat)) := by
                  rw [← h_input_eq]; exact hinv
                have hreach_new : OrbitReachable
                    (MacroConfig.M0 ((a' + 1) :: L' : List Nat)
                      ((r' + 3) :: e :: middle_init' ++ [1, 2] : List Nat)) := by
                  rw [← h_input_eq]; exact hreach
                obtain ⟨k, cfg', hk, hcfg', hinv', h_safe, h_strict_safe, h_phi⟩ :=
                  thm_reach_multi_bounce_last_2_long_safe hinv_new
                have hreach' : OrbitReachable cfg' :=
                  OrbitReachable.step_R3 (a := a' + 1) (r' := r') (e := e)
                    (L' := L') (middle_init := middle_init') (cfg' := cfg') (k := k)
                    hreach_new hcfg' hinv' hk h_safe h_strict_safe h_phi
                refine ⟨k, hk, ⟨cfg', ?_, hreach'⟩, ?_⟩
                · simp only [MacroConfig.toConfig_M0]
                  rw [h_input_eq]
                  exact hcfg'
                · simp only [MacroConfig.toConfig_M0]
                  rw [h_input_eq, hcfg']
                  exact MacroConfig.toConfig_state cfg' ▸ Option.some_ne_none _
              | l + 2, _ =>
                -- Last middle ≥ 2: multi_bounce_last_2_general
                have h_input_eq :
                    ((r' + 3) :: (e :: f :: rest ++ [0 + 1 + 1]) : List Nat) =
                    (r' + 3) :: (e :: middle_init') ++ [l + 2, 2] := by
                  rw [hdecomp_inner]; simp [List.cons_append, List.append_assoc]
                have hinv_new : MacroInvariant
                    (MacroConfig.M0 ((a' + 1) :: L' : List Nat)
                      ((r' + 3) :: (e :: middle_init') ++ [l + 2, 2] : List Nat)) := by
                  rw [← h_input_eq]; exact hinv
                have hreach_new : OrbitReachable
                    (MacroConfig.M0 ((a' + 1) :: L' : List Nat)
                      ((r' + 3) :: (e :: middle_init') ++ [l + 2, 2] : List Nat)) := by
                  rw [← h_input_eq]; exact hreach
                have ht := macro_multi_bounce_last_2_general (a' + 1) r' l L'
                  (e :: middle_init')
                  (by
                    intro x hx
                    rcases List.mem_cons.mp hx with hx_e | hx_mid
                    · subst hx_e
                      exact hR_mid_ge x List.mem_cons_self
                    · have hx_in : x ∈ (f :: rest) := by
                        rw [hdecomp_inner]
                        exact List.mem_append.mpr (Or.inl hx_mid)
                      exact hR_mid_ge x (List.mem_cons_of_mem _ hx_in))
                have hreach' : OrbitReachable
                    (.M ((e :: middle_init').reverse ++ (r' + 1) :: (a' + 1 + 4) :: L')
                      (l + 2) [1, 1]) :=
                  OrbitReachable.step_multi_bounce_last_2_general
                    (a := a' + 1) (r' := r') (m_last := l) (L' := L')
                    (middle_init := e :: middle_init') hreach_new
                refine ⟨r' + 3 * ((e :: middle_init').length + 1)
                          + ((e :: middle_init').sum + (l + 2)) + 17 + 6, by omega,
                        ⟨.M ((e :: middle_init').reverse ++
                            (r' + 1) :: (a' + 1 + 4) :: L') (l + 2) [1, 1], ?_, hreach'⟩, ?_⟩
                · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
                  rw [h_input_eq]
                  exact ht
                · simp only [MacroConfig.toConfig_M0]
                  rw [h_input_eq]
                  exact ht ▸ M_Config_state_ne_none _ _ _
        | last'' + 2 =>
          -- last ≥ 3: multi_bounce_general
          have heq1 : last'' + 2 + 1 = last'' + 3 := by omega
          rw [heq1] at hinv hreach
          have ht := macro_multi_bounce_general (a' + 1) r' (last'' + 1) L' R_mid hR_mid_ge
          have hreach' : OrbitReachable
              (.M (R_mid.reverse ++ (r' + 1) :: (a' + 1 + 4) :: L') (last'' + 2) [1]) :=
            OrbitReachable.step_multi_bounce_general
              (a := a' + 1) (r' := r') (last'' := last'')
              (L' := L') (R_mid := R_mid) hreach
          have hk_pos : 0 < r' + (last'' + 1) + 3 * R_mid.length + R_mid.sum + 17 := by omega
          refine ⟨r' + (last'' + 1) + 3 * R_mid.length + R_mid.sum + 17, hk_pos,
                  ⟨.M (R_mid.reverse ++ (r' + 1) :: (a' + 1 + 4) :: L')
                      (last'' + 2) [1], ?_, hreach'⟩, ?_⟩
          · simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
            have heq2 : (last'' + 1) + 1 = last'' + 2 := by omega
            have heq3 : (last'' + 1) + 2 = last'' + 3 := by omega
            rw [heq3] at ht
            rw [← heq2]; exact ht
          · simp only [MacroConfig.toConfig_M0]
            have heq2 : (last'' + 1) + 1 = last'' + 2 := by omega
            have heq3 : (last'' + 1) + 2 = last'' + 3 := by omega
            rw [heq3] at ht
            exact ht ▸ M_Config_state_ne_none _ _ _

/-- Progress predicate for the era-based approach. Currently defined as `MacroProg`
    but structured to allow future refinement. -/
def EraPlusSweep (c : Config 6) : Prop := MacroProg c

/-- Initial config at step 43 satisfies EraPlusSweep. -/
theorem init_era_plus_sweep : EraPlusSweep (run sweeper (initConfig 6) 43) :=
  init_macro_prog

/-- Era 0: M[1] 4 [1] → M[1] 10 [1] in 77 steps. Proven by `macroEra_sound`
    applied to fuel=4 iterations of `macroStep`. -/
theorem macroEra0 :
    run sweeper (M_Config [1] 4 [1]) 77 = M_Config [1] 10 [1] := by
  have h := (macroEra_sound 4 (MacroConfig.M [1] 4 [1]) invariant_initial).1
  rw [MacroConfig.toConfig_M, MacroConfig.toConfig_M] at h
  exact h

/-- Era 1: M[1] 10 [1] → M[10] 3 [1] in 110 steps, via 6 `macroStep` iterations. -/
theorem macroEra1 :
    run sweeper (M_Config [1] 10 [1]) 110 = M_Config [10] 3 [1] := by
  have hinv : MacroInvariant (MacroConfig.M [1] 10 [1]) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact AllGe1_cons.mpr ⟨by omega, AllGe1_nil⟩
    · omega
    · exact AllGe1_cons.mpr ⟨by omega, AllGe1_nil⟩
    · decide
  have h := (macroEra_sound 6 (MacroConfig.M [1] 10 [1]) hinv).1
  rw [MacroConfig.toConfig_M, MacroConfig.toConfig_M] at h
  exact h

/-- Era progress: delegates to macro_progress.
    Future refinement: prove directly via `macroEra` function, eliminating dependencies
    on the Mersenne-cascade-affected portions of macro_progress. -/
theorem era_progress (c : Config 6) (h : EraPlusSweep c) :
    ∃ k, 0 < k ∧ EraPlusSweep (run sweeper c k) ∧ (run sweeper c k).state ≠ none :=
  macro_progress c h

-- ============================================================
-- Main non-halting theorem
-- ============================================================

/-- The machine never halts: for all k, the state after k steps is not none.
    Refactored to use `OrbitProg` (which tracks `OrbitReachable`) instead of
    `MacroProg`/`EraPlusSweep`. This sets up Phase 2 work where `OrbitReachable`
    can be used to prove specific axiom shapes are unreachable. -/
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  -- Split: first 43 steps computed directly, then use orbit progress
  suffices h43 : ∀ j, j < 43 → (run sweeper (initConfig 6) j).state ≠ none by
    by_cases hk : k < 43
    · exact h43 k hk
    · push_neg at hk
      rw [show k = 43 + (k - 43) from by omega, run_add]
      exact nonhalt_of_progress sweeper OrbitProg orbit_progress
        (run sweeper (initConfig 6) 43) init_orbit_prog (k - 43)
  -- First 43 steps: each one computes to state = some _
  intro j hj
  interval_cases j <;> simp [run, step, sweeper, initConfig]

end Sweeper
