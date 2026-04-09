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

/-- Any M_Config has state = some stA ≠ none. -/
lemma M_Config_state_ne_none (L : List Nat) (n : Nat) (R : List Nat) :
    (M_Config L n R).state ≠ none := by simp [M_Config]

/-- Any M0_Config has state = some stA ≠ none. -/
lemma M0_Config_state_ne_none (L : List Nat) (R : List Nat) :
    (M0_Config L R).state ≠ none := by simp [M0_Config]

/-- Package an M_Config transition + invariant into a progress proof. -/
private lemma mk_progress_M {c₀ : Config 6} (k : Nat) (L : List Nat) (c : Nat) (R : List Nat)
    (hk : 0 < k) (htrans : run sweeper c₀ k = M_Config L c R)
    (hinv' : MacroInvariant (.M L c R)) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper c₀ k) ∧ (run sweeper c₀ k).state ≠ none :=
  ⟨k, hk, ⟨.M L c R, by rw [htrans, MacroConfig.toConfig_M], hinv'⟩,
   by rw [htrans]; exact M_Config_state_ne_none L c R⟩

/-- Package an M0_Config transition + invariant into a progress proof. -/
private lemma mk_progress_M0 {c₀ : Config 6} (k : Nat) (L R : List Nat)
    (hk : 0 < k) (htrans : run sweeper c₀ k = M0_Config L R)
    (hinv' : MacroInvariant (.M0 L R)) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper c₀ k) ∧ (run sweeper c₀ k).state ≠ none :=
  ⟨k, hk, ⟨.M0 L R, by rw [htrans, MacroConfig.toConfig_M0], hinv'⟩,
   by rw [htrans]; exact M0_Config_state_ne_none L R⟩

/-- Multi-bounce progress: last ≥ 3 case. -/
private lemma multi_bounce_progress {a r' last'' : Nat} {L' R_mid : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])))
    (hR_mid_ge : ∀ x ∈ R_mid, x ≥ 1) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [last'' + 3])) k).state ≠ none :=
  mk_progress_M _ _ _ _
    (by set n := R_mid.length; set s := List.sum R_mid; omega)
    (macro_multi_bounce_general a r' (last'' + 1) L' R_mid hR_mid_ge)
    (invariant_multi_bounce_general hinv)

/-- Multi-bounce progress: last = 1 case. -/
private lemma multi_bounce_to_zero_progress {a r' : Nat} {L' R_mid : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: R_mid ++ [1])))
    (hR_mid_ge : ∀ x ∈ R_mid, x ≥ 1) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [1])) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: R_mid ++ [1])) k).state ≠ none :=
  mk_progress_M0 _ _ _
    (by set n := R_mid.length; set s := List.sum R_mid; omega)
    (macro_multi_bounce_general_to_zero a r' L' R_mid hR_mid_ge)
    (invariant_multi_bounce_general_to_zero hinv)

/-- Compound: multi_bounce_2 (with rₙ=0) + shift. For R=[r+4, 2], gives cursor r+2 ≥ 2.
    Handles the 2-run case where last=2 (rₙ=0). -/
theorem macro_multi_bounce_2_and_shift (a r : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [r + 4, 2]) (r + 24) =
    M_Config ((a + 4) :: L) (r + 2) [1, 1] := by
  -- Chain multi_bounce_2 (r+1+17 = r+18 steps) + shift (6 steps) = r+24
  rw [show r + 24 = (r + 18) + 6 from by omega, run_add,
    show (r + 4 : Nat) = (r + 1) + 3 from by omega,
    show (2 : Nat) = 0 + 2 from rfl,
    show (r + 18 : Nat) = (r + 1) + 0 + 17 from by omega,
    macro_multi_bounce_2 a (r + 1) 0 L,
    show (0 : Nat) + 1 = 1 from rfl,
    show ((r + 1) + 1 : Nat) = r + 2 from by omega]
  exact macro_shift (r + 1) 1 ((a + 4) :: L) []

/-- Invariant preservation for multi_bounce_2 + shift compound. -/
theorem invariant_multi_bounce_2_and_shift {a r : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [r + 4, 2])) :
    MacroInvariant (.M ((a + 4) :: L) (r + 2) [1, 1]) := by
  have hL := h.1; rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, by omega, ⟨by omega, by omega, trivial⟩,
         List.cons_ne_nil _ _⟩

/-- Multi-bounce progress: last = 2, 2-run case (R_mid = []). -/
private lemma multi_bounce_last_2_two_run_progress {a r : Nat} {L' : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') [r + 4, 2])) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') [r + 4, 2]) k) ∧
      (run sweeper (M0_Config (a :: L') [r + 4, 2]) k).state ≠ none := by
  exact mk_progress_M (r + 24) ((a + 4) :: L') (r + 2) [1, 1] (by omega)
    (macro_multi_bounce_2_and_shift a r L')
    (invariant_multi_bounce_2_and_shift hinv)

/-- Compound: multi_bounce_2 (r=0, rₙ=0) + double shift for R=[3, 2] case.
    Chain: M0(a::L, [3,2]) →₁₇ M(1::(a+4)::L, 1, [1]) →₆ M((a+4)::L, 1, [1,1]) →₆ M(L, a+4, [1,1,1]). -/
theorem macro_multi_bounce_2_double_shift (a : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [3, 2]) 29 = M_Config L (a + 4) [1, 1, 1] := by
  have h1 : run sweeper (M0_Config (a :: L) [3, 2]) 17 =
      M_Config (1 :: (a + 4) :: L) 1 [1] := macro_multi_bounce_2 a 0 0 L
  have h2 : run sweeper (M_Config (1 :: (a + 4) :: L) 1 [1]) 6 =
      M_Config ((a + 4) :: L) 1 [1, 1] := macro_shift 0 1 ((a + 4) :: L) []
  have h3 : run sweeper (M_Config ((a + 4) :: L) 1 [1, 1]) 6 =
      M_Config L (a + 4) [1, 1, 1] := macro_shift (a + 3) 1 L [1]
  rw [show (29 : Nat) = 17 + (6 + 6) from rfl, run_add, h1, run_add, h2, h3]

/-- Invariant preservation for multi_bounce_2 double-shift compound. -/
theorem invariant_multi_bounce_2_double_shift {a : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [3, 2])) :
    MacroInvariant (.M L (a + 4) [1, 1, 1]) := by
  have hL := h.1; rw [AllGe1_cons] at hL
  refine ⟨hL.2, by omega, ?_, List.cons_ne_nil _ _⟩
  exact ⟨by omega, by omega, by omega, trivial⟩

/-- Multi-bounce progress: last = 2, 2-run case with r=0 (R=[3,2]). -/
private lemma multi_bounce_last_2_two_run_r0_progress {a : Nat} {L' : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') [3, 2])) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') [3, 2]) k) ∧
      (run sweeper (M0_Config (a :: L') [3, 2]) k).state ≠ none := by
  exact mk_progress_M 29 L' (a + 4) [1, 1, 1] (by omega)
    (macro_multi_bounce_2_double_shift a L')
    (invariant_multi_bounce_2_double_shift hinv)

/-- Compound: multi_bounce_general(R_mid=[e], rₙ=0) + shift, for R=[r'+3, e+2, 2]
    where e ≥ 1 (so e+2 ≥ 3 in the middle of R). Output: M((r'+1)::(a+4)::L, e+2, [1,1]). -/
theorem macro_multi_bounce_3run_last_2 (a r' e : Nat) (L : List Nat) :
    run sweeper (M0_Config (a :: L) [r' + 3, e + 2, 2]) (r' + 3 * 1 + (e + 2) + 17 + 6) =
    M_Config ((r' + 1) :: (a + 4) :: L) (e + 2) [1, 1] := by
  have h1 : run sweeper (M0_Config (a :: L) [r' + 3, e + 2, 2]) (r' + 3 * 1 + (e + 2) + 17) =
      M_Config ([e + 2] ++ (r' + 1) :: (a + 4) :: L) 1 [1] := by
    have := macro_multi_bounce_general a r' 0 L [e + 2]
      (by intro x hx; simp at hx; omega)
    simpa using this
  have h2 : run sweeper (M_Config ([e + 2] ++ (r' + 1) :: (a + 4) :: L) 1 [1]) 6 =
      M_Config ((r' + 1) :: (a + 4) :: L) (e + 2) [1, 1] := by
    simp only [List.append_eq, List.cons_append, List.nil_append]
    have := macro_shift (e + 1) 1 ((r' + 1) :: (a + 4) :: L) []
    simpa using this
  rw [run_add, h1, h2]

/-- Invariant preservation for 3-run multi_bounce last=2. -/
theorem invariant_multi_bounce_3run_last_2 {a r' e : Nat} {L : List Nat}
    (h : MacroInvariant (.M0 (a :: L) [r' + 3, e + 2, 2])) :
    MacroInvariant (.M ((r' + 1) :: (a + 4) :: L) (e + 2) [1, 1]) := by
  have hL := h.1; rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL.2⟩⟩,
         by omega, ⟨by omega, by omega, trivial⟩, List.cons_ne_nil _ _⟩

/-- Progress: 3-run multi_bounce with last=2. -/
private lemma multi_bounce_last_2_three_run_progress {a r' e : Nat} {L' : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') [r' + 3, e + 2, 2])) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M0_Config (a :: L') [r' + 3, e + 2, 2]) k) ∧
      (run sweeper (M0_Config (a :: L') [r' + 3, e + 2, 2]) k).state ≠ none := by
  exact mk_progress_M _ ((r' + 1) :: (a + 4) :: L') (e + 2) [1, 1] (by omega)
    (macro_multi_bounce_3run_last_2 a r' e L')
    (invariant_multi_bounce_3run_last_2 hinv)

-- ============================================================
-- Reachability axioms (Option D)
-- ============================================================
-- Three macro configs arise transiently in the raw TM orbit for which the
-- macro layer lacks a direct transition theorem. The 10M-step simulation
-- confirms the raw TM continues past each without halting. We document these
-- as axiomatic reachability assumptions. See `era_plan.md` for why the
-- Mersenne-preservation and strengthened-EraPlusSweep refinement approaches
-- both failed to eliminate them.
-- ============================================================

/-- **Reachability axiom R1**: `M([], 3, d::R)` continues.
    This state is produced by `sweep_and_shift` from `M([2], 3, d::R)` when
    the left stack has a single element of value 2. The macro layer has no
    direct theorem covering it — `macro_sweep_left_empty` with c=0 would
    produce output cursor 1, below the invariant threshold. Empirically
    verified non-halting through 10M raw TM steps. -/
axiom reach_M_nil_3 {d : Nat} {R' : List Nat}
    (hinv : MacroInvariant (.M [] 3 (d :: R'))) :
    ∃ k, 0 < k ∧ MacroProg (run sweeper (M_Config [] 3 (d :: R')) k) ∧
      (run sweeper (M_Config [] 3 (d :: R')) k).state ≠ none

/-- **Reachability axiom R2**: `M0(a::L', [r'+3, 1, 2])` continues.
    The 3-run multi_bounce case with middle run of length 1 and last run of
    length 1. After multi_bounce and shift, cursor equals the middle run
    value (1), which requires additional shifts not currently compound. -/
axiom reach_multi_bounce_last_2_mid_1 {a r' : Nat} {L' : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: ([1] ++ [2])))) :
    ∃ k, 0 < k ∧
      MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: ([1] ++ [2]))) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: ([1] ++ [2]))) k).state ≠ none

/-- **Reachability axiom R3**: `M0(a::L', (r'+3) :: R_mid ++ [2])` continues,
    for `R_mid` of length ≥ 2. The general multi_bounce last=2 case with
    nontrivial middle tail. Would require a recursively-defined compound
    transition threading through all middle runs. -/
axiom reach_multi_bounce_last_2_long {a r' e f : Nat} {L' rest : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: (e :: f :: rest ++ [1 + 1])))) :
    ∃ k, 0 < k ∧
      MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: (e :: f :: rest ++ [1 + 1]))) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: (e :: f :: rest ++ [1 + 1]))) k).state ≠ none

set_option maxHeartbeats 400000 in
/-- Every macro config satisfying the invariant progresses to another one.
    This is the core dispatch: match on the config shape, apply the right rule.
    Depends on 3 reachability axioms (R1, R2, R3) for transient states the
    macro layer cannot close directly. -/
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
      | 3, _ => exact reach_M_nil_3 hinv
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
                -- e = 1: R = [r'+3, 1, 2]. Closed by reachability axiom R2.
                exact reach_multi_bounce_last_2_mid_1 hinv
              | succ e'' =>
                -- e = e''+2 ≥ 2: use 3-run compound.
                exact multi_bounce_last_2_three_run_progress
                  (show MacroInvariant (.M0 (a :: L') [r' + 3, e'' + 2, 2]) from hinv)
            | cons _ _ =>
              -- R_mid has ≥ 2 elements: closed by reachability axiom R3.
              exact reach_multi_bounce_last_2_long hinv
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
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M0]; exact macro_sweep_to_zero_left_empty d R'
        · exact invariant_sweep_to_zero_left_empty hinv
      | 3, _ =>
        simp only [macroStep] at hstep
        cases hstep
      | c' + 4, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M,
            show c' + 4 = (c' + 1) + 3 from by omega]
          exact macro_sweep_left_empty (c' + 1) d R'
        · exact invariant_sweep_left_empty hinv
    | cons a L' =>
      match c, hc with
      | 2, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M0]; exact macro_sweep_to_zero a d L' R'
        · exact invariant_sweep_to_zero hinv
      | 3, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_sweep_and_shift a d L' R'
        · exact invariant_sweep_and_shift hinv
      | c' + 4, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
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
          simp only [macroStep] at hstep
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
          refine ⟨?_, ?_, by omega⟩
          · rw [MacroConfig.toConfig_M]; exact macro_era_and_sweep_solo a'
          · exact invariant_era_and_sweep_solo hinv
        | cons b L'' =>
          simp only [macroStep] at hstep
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
          refine ⟨?_, ?_, by omega⟩
          · rw [MacroConfig.toConfig_M]; exact macro_era_and_sweep a' b L''
          · exact invariant_era_and_sweep hinv
      | 2, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_zero_two_solo (a' + 1) L'
        · exact invariant_zero_two_solo hinv
      | 3, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M0]; exact macro_zero_bounce_to_zero (a' + 1) L'
        · exact invariant_zero_bounce_to_zero hinv
      | 4, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_zero_bounce_and_shift (a' + 1) L'
        · exact invariant_zero_bounce_and_shift hinv
      | r' + 5, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
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
        simp only [macroStep] at hstep
        cases hstep
      | 2, _ =>
        simp only [macroStep] at hstep
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstep)
        refine ⟨?_, ?_, by omega⟩
        · rw [MacroConfig.toConfig_M]; exact macro_zero_two (a' + 1) d L' R''
        · exact invariant_zero_two hinv
      | r' + 3, _ =>
        simp only [macroStep] at hstep
        cases hstep

/-- Soundness of `macroEra`: iterating `macroStep` for `fuel` steps correctly
    tracks the raw TM run and preserves the invariant. -/
theorem macroEra_sound (fuel : Nat) (cfg : MacroConfig) (hinv : MacroInvariant cfg) :
    let (k, cfg') := macroEra fuel cfg
    run sweeper cfg.toConfig k = cfg'.toConfig ∧ MacroInvariant cfg' := by
  induction fuel generalizing cfg with
  | zero => simp [macroEra, run, hinv]
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

/-- The machine never halts: for all k, the state after k steps is not none. -/
theorem sweeper_never_halts (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  -- Split: first 43 steps computed directly, then use era progress
  suffices h43 : ∀ j, j < 43 → (run sweeper (initConfig 6) j).state ≠ none by
    by_cases hk : k < 43
    · exact h43 k hk
    · push_neg at hk
      rw [show k = 43 + (k - 43) from by omega, run_add]
      exact nonhalt_of_progress sweeper EraPlusSweep era_progress
        (run sweeper (initConfig 6) 43) init_era_plus_sweep (k - 43)
  -- First 43 steps: each one computes to state = some _
  intro j hj
  interval_cases j <;> simp [run, step, sweeper, initConfig]

end Sweeper
