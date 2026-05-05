/-
Φ-monotonicity at the `macroStep` dispatch level (Stage 3 of the plan in
`LOG.md`).

`macroStep_phi_nondec` lifts the per-rule Φ-deltas (Stage 2, in `phi.lean`)
to the dispatched form: for any one-step macro transition, output Φ ≥ input Φ.
The strict variant `macroStep_phi_strict_at_era` shows ΔΦ ≥ 4 whenever the
input has the era-boundary shape `M0 _ [1]` (the only `macroStep` arms that
fire there are `era_and_sweep` and `era_and_sweep_solo`, both Δ=4).

Each case discharges by pattern-extracting the input/output via `ms_simp` and
then unfolding Φ to a linear arithmetic identity closed by `omega`. The
per-rule lemmas of `phi.lean` are not invoked directly (the arithmetic is
mechanical at this level), but they document the same per-rule deltas at a
named layer.
-/

import phi
import progress

namespace Sweeper

open BusyLean

set_option maxHeartbeats 400000 in
/-- One macro step never decreases Φ. The proof case-splits on the
    `macroStep` dispatch (12 dispatched arms + ~12 `none` arms); each
    dispatched arm closes by `ms_simp` + arithmetic. -/
theorem macroStep_phi_nondec (cfg cfg' : MacroConfig) (k : Nat)
    (h : macroStep cfg = some (k, cfg')) :
    cfg.phi ≤ cfg'.phi := by
  cases cfg with
  | M L c R =>
    cases R with
    | nil => ms_done at h
    | cons d R' =>
      cases L with
      | nil =>
        match c with
        | 0 => ms_done at h
        | 1 => ms_done at h
        | 2 =>
          ms_simp at h; obtain ⟨rfl, rfl⟩ := h
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                     List.sum_cons, List.sum_nil]
          omega
        | 3 => ms_done at h
        | c' + 4 =>
          ms_simp at h; obtain ⟨rfl, rfl⟩ := h
          simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
          omega
      | cons a L' =>
        match c with
        | 0 => ms_done at h
        | 1 => ms_done at h
        | 2 =>
          ms_simp at h; obtain ⟨rfl, rfl⟩ := h
          simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons]
          omega
        | 3 =>
          ms_simp at h; obtain ⟨rfl, rfl⟩ := h
          simp only [MacroConfig.phi_M, List.sum_cons]
          omega
        | c' + 4 =>
          ms_simp at h; obtain ⟨rfl, rfl⟩ := h
          simp only [MacroConfig.phi_M, List.sum_cons]
          omega
  | M0 L R =>
    cases L with
    | nil => ms_done at h
    | cons a L' =>
      cases R with
      | nil => ms_done at h
      | cons r R' =>
        cases R' with
        | nil =>
          match r with
          | 0 => ms_done at h
          | 1 =>
            match a with
            | 0 =>
              cases L' with
              | nil => ms_done at h
              | cons _ _ => ms_done at h
            | a' + 1 =>
              cases L' with
              | nil =>
                ms_simp at h; obtain ⟨rfl, rfl⟩ := h
                simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                           List.sum_cons, List.sum_nil]
                omega
              | cons b L'' =>
                ms_simp at h; obtain ⟨rfl, rfl⟩ := h
                simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                           List.sum_cons, List.sum_nil]
                omega
          | 2 =>
            ms_simp at h; obtain ⟨rfl, rfl⟩ := h
            simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                       List.sum_cons, List.sum_nil]
            omega
          | 3 =>
            ms_simp at h; obtain ⟨rfl, rfl⟩ := h
            simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
            omega
          | 4 =>
            ms_simp at h; obtain ⟨rfl, rfl⟩ := h
            simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                       List.sum_cons, List.sum_nil]
            omega
          | r' + 5 =>
            ms_simp at h; obtain ⟨rfl, rfl⟩ := h
            simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                       List.sum_cons, List.sum_nil]
            omega
        | cons d R'' =>
          match r with
          | 0 => ms_done at h
          | 1 => ms_done at h
          | 2 =>
            ms_simp at h; obtain ⟨rfl, rfl⟩ := h
            simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_cons]
            omega
          | _ + 3 => ms_done at h

/-- Strict Φ-increase across an era-completion step. When `cfg` has the
    era-boundary shape `M0 _ [1]` and `macroStep` dispatches, the only firing
    arms are `era_and_sweep` and `era_and_sweep_solo`, both giving ΔΦ = +4. -/
theorem macroStep_phi_strict_at_era (L : List Nat) (cfg' : MacroConfig) (k : Nat)
    (h : macroStep (.M0 L [1]) = some (k, cfg')) :
    (MacroConfig.M0 L [1]).phi + 4 ≤ cfg'.phi := by
  cases L with
  | nil => ms_done at h
  | cons a L' =>
    match a with
    | 0 =>
      cases L' with
      | nil => ms_done at h
      | cons _ _ => ms_done at h
    | a' + 1 =>
      cases L' with
      | nil =>
        ms_simp at h; obtain ⟨rfl, rfl⟩ := h
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                   List.sum_cons, List.sum_nil]
        omega
      | cons b L'' =>
        ms_simp at h; obtain ⟨rfl, rfl⟩ := h
        simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
                   List.sum_cons, List.sum_nil]
        omega

-- ============================================================
-- Stage 4: lift to iterated macroEra and to raw `run sweeper`
-- ============================================================

/-- Φ is non-decreasing along any iterated `macroEra` chain. Induction on
    `fuel`; the step case chains `macroStep_phi_nondec` with the inductive
    hypothesis via transitivity. Stops cleanly when `macroStep` returns
    `none` (no progress, so Φ trivially preserved).

    No `MacroInvariant` needed: the lemma is a pure consequence of
    `macroStep`'s dispatch shape. -/
theorem macroEra_phi_nondec (fuel : Nat) (cfg : MacroConfig) :
    cfg.phi ≤ (macroEra fuel cfg).2.phi := by
  induction fuel generalizing cfg with
  | zero => simp [macroEra]
  | succ fuel' ih =>
    rw [macroEra]
    cases hstep : macroStep cfg with
    | none => simp
    | some kc =>
      obtain ⟨k, cfg'⟩ := kc
      have h1 : cfg.phi ≤ cfg'.phi := macroStep_phi_nondec cfg cfg' k hstep
      have h2 : cfg'.phi ≤ (macroEra fuel' cfg').2.phi := ih cfg'
      exact le_trans h1 h2

/-- Combined raw-run + Φ-monotonicity: running the raw TM along the macro
    chain produces a config with Φ ≥ start. The `let`-form mirrors
    `macroEra_sound` for compositional use. -/
theorem run_macroEra_phi_nondec (fuel : Nat) (cfg : MacroConfig)
    (hinv : MacroInvariant cfg) :
    let (k, cfg') := macroEra fuel cfg
    run sweeper cfg.toConfig k = cfg'.toConfig ∧
      MacroInvariant cfg' ∧ cfg.phi ≤ cfg'.phi := by
  obtain ⟨hrun, hinv'⟩ := macroEra_sound fuel cfg hinv
  exact ⟨hrun, hinv', macroEra_phi_nondec fuel cfg⟩

end Sweeper
