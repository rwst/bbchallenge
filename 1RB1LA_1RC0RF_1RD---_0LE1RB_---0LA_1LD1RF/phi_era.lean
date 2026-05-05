/-
Stage 5 of the Φ plan (`LOG.md`, 2026-05-05): strict Φ-increase across
era boundaries.

Given an era-start `e : EraStartConfig` (shape `M(L, e.c, [1])` with `L ≠ []`
and `c ≥ 4`), and a macroEra trajectory that reaches an era-end M0 shape
`M0(L_pre, [1])` followed by one further `macroStep` (which dispatches as
`era_and_sweep`/`era_and_sweep_solo`), the resulting config has
`Φ ≥ Φ(e.toMacro) + 4`.

The proof composes:
  • Stage 4 `macroEra_phi_nondec`: Φ non-decreasing along the within-era chain.
  • Stage 3 `macroStep_phi_strict_at_era`: ΔΦ = +4 across the era-end step.

A corollary specializes to the case where the post-step config is itself an
`EraStartConfig` (the orbital case): `phi_strict_between_era_starts`.
-/

import phi_progress
import era

namespace Sweeper

open BusyLean

/-- Φ strictly increases by ≥ 4 across an era-boundary step. The macroEra
    chain from `e.toMacro` reaches an era-end `M0(L, [1])` shape after `fuel`
    steps; one further `macroStep` (an `era_and_sweep` variant, ΔΦ = +4)
    completes the era transition.

    Composes `macroEra_phi_nondec` (Φ non-decreasing along the chain) with
    `macroStep_phi_strict_at_era` (the +4 jump at era-end). -/
theorem phi_strict_across_era_step
    (e : EraStartConfig) (fuel : Nat) (L : List Nat)
    (h_pre : (macroEra fuel e.toMacro).2 = .M0 L [1])
    (cfg' : MacroConfig) (k : Nat)
    (h_step : macroStep (.M0 L [1]) = some (k, cfg')) :
    e.toMacro.phi + 4 ≤ cfg'.phi := by
  have h1 : e.toMacro.phi ≤ (MacroConfig.M0 L [1]).phi := by
    have := macroEra_phi_nondec fuel e.toMacro
    rw [h_pre] at this
    exact this
  have h2 : (MacroConfig.M0 L [1]).phi + 4 ≤ cfg'.phi :=
    macroStep_phi_strict_at_era L cfg' k h_step
  omega

/-- Specialization of `phi_strict_across_era_step` to the orbital case where
    the post-step config is itself an `EraStartConfig`. This is the form
    typically produced by the orbit dynamics (`macroStep_M0_R1_produces_era_start`
    confirms `era_and_sweep` outputs are always era-starts). -/
theorem phi_strict_between_era_starts
    (e e' : EraStartConfig) (fuel : Nat) (L : List Nat) (k : Nat)
    (h_pre : (macroEra fuel e.toMacro).2 = .M0 L [1])
    (h_step : macroStep (.M0 L [1]) = some (k, e'.toMacro)) :
    e.toMacro.phi + 4 ≤ e'.toMacro.phi :=
  phi_strict_across_era_step e fuel L h_pre _ k h_step

end Sweeper
