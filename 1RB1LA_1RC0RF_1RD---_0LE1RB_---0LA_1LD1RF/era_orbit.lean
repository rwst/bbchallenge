/-
Era-graded lifting of `OrbitReachable` (Stage A of `plan-era-graded-not_R1.md`).

This file develops the relationship between orbit-reachable era-shape configs
(`M(L, c, [1])` from `EraStartConfig`) and their predecessors in the
orbit. The end goal is to prove `OrbitReachable.not_R1` via era-graded
forward analysis:

  • A1.0 (this file): structural Φ ≥ 6 on era-starts.
  • A1.1: every `macroStep` producing era-shape has ΔΦ ≥ +2.
  • A1.2: every orbit-reachable era-shape has a Φ-strict orbit-reachable
    predecessor (or it's `init`).
  • A2 (later): Φ ≥ 6 + 2n bound on era-shape configs at depth n.
  • B+C+D+F+G (later): R1 closure.

The Φ-strict-predecessor framework (A1.2) bounds the Φ jump per era-step
across all OrbitReachable constructors that produce era-shape outputs:
`step_macro` (D6, D7, D8 with proper L, D11 with proper c),
`step_multi_bounce_general` (output R = [1]). The `step_R3` constructor
produces R with length ≥ 2 (after at least one shift), so it doesn't
produce era-shape. The `step_R1` case requires joint reasoning with
`not_R1` (deferred).
-/

import phi_era
import phase2

namespace Sweeper

open BusyLean

-- ============================================================
-- A1.0: structural Φ ≥ 6 on era-starts
-- ============================================================

/-- A non-empty list of ≥1 naturals has sum ≥ 1. -/
private lemma AllGe1_sum_ge_one_of_ne_nil
    {L : List Nat} (hL : AllGe1 L) (hL_ne : L ≠ []) : L.sum ≥ 1 := by
  cases L with
  | nil => exact absurd rfl hL_ne
  | cons a L' =>
    have ha := (AllGe1_cons.mp hL).1
    simp [List.sum_cons]; omega

/-- Every era-start has Φ ≥ 6 by structure: `L.sum ≥ 1` (from `L ≠ []`
    and `AllGe1 L`), `R = [1]` so `R.sum = 1`, and `c ≥ 4`. -/
theorem EraStartConfig.phi_ge_six (e : EraStartConfig) : e.toMacro.phi ≥ 6 := by
  have h_L_sum := AllGe1_sum_ge_one_of_ne_nil e.L_all_ge1 e.L_ne_nil
  have hc := e.c_ge4
  simp only [EraStartConfig.toMacro, MacroConfig.phi_M,
             List.sum_cons, List.sum_nil]
  omega

-- ============================================================
-- A1.1: macroStep producing proper era-shape has ΔΦ ≥ +2
-- ============================================================

/-- **A1.1**: any `macroStep` whose output is era-shape `M(L_out, c_out, [1])`
    has Φ-jump ≥ +2. Stronger than the plan's "proper era-shape" form —
    the proof shows Δ ≥ +2 even for degenerate era-shapes (L=[] from D8
    with singleton L_pre, c<4 from D11 with z<2). The productive
    producers are D6 (era_and_sweep, ΔΦ=+4), D7 (era_and_sweep_solo,
    ΔΦ=+4), D8 (zero_two_solo, ΔΦ=+2), D11 (zero_bounce, ΔΦ=+2). All
    other dispatches either return `none`, produce M0 outputs,
    R-length ≥ 2 outputs, or produce R=[1] only with `d=0` invariant
    violations. -/
theorem macroStep_to_era_shape_phi_strict
    {cfg cfg' : MacroConfig} {k : Nat}
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, cfg'))
    {L_out : List Nat} {c_out : Nat}
    (hcfg' : cfg' = .M L_out c_out [1]) :
    cfg.phi + 2 ≤ cfg'.phi := by
  rcases macroStep_eq_some_cases cfg k cfg' h with
    ⟨a, L', d, R', hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, _, htgt⟩
  | ⟨a, c', L', d, R', hcfg, _, htgt⟩
  | ⟨d, R', hcfg, _, htgt⟩
  | ⟨c', d, R', hcfg, _, htgt⟩
  | ⟨a, b, L', hcfg, _, htgt⟩
  | ⟨a, hcfg, _, htgt⟩
  | ⟨a, L', hcfg, _, htgt⟩
  | ⟨a, L', hcfg, _, htgt⟩
  | ⟨a, L', hcfg, _, htgt⟩
  | ⟨a, z, L', hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, _, htgt⟩
  · -- D1 sweep_to_zero: target = M0, contradicts hcfg' = M.
    exfalso; subst htgt; injection hcfg'
  · -- D2 sweep_and_shift: target R = 1::(d+1)::R', length ≥ 2 ≠ [1].
    exfalso
    subst htgt
    injection hcfg' with _ _ hR_eq
    injection hR_eq with _ hR'_eq
    exact (List.cons_ne_nil _ _) hR'_eq
  · -- D3 sweep: target R = (d+1)::R'; for R = [1] need d=0, invariant violation.
    exfalso
    subst htgt
    injection hcfg' with _ _ hR_eq
    injection hR_eq with hd_eq _
    -- hd_eq : d + 1 = 1 → d = 0. Predecessor cfg has R = d::R' with d ≥ 1.
    subst hcfg
    have hd_inv := (AllGe1_cons.mp hinv.2.2.1).1
    omega
  · -- D4 sweep_to_zero_left_empty: target = M0, contradicts hcfg' = M.
    exfalso; subst htgt; injection hcfg'
  · -- D5 sweep_left_empty: target R = (d+1)::R'; for R=[1] need d=0, invariant.
    exfalso
    subst htgt
    injection hcfg' with _ _ hR_eq
    injection hR_eq with hd_eq _
    subst hcfg
    have hd_inv := (AllGe1_cons.mp hinv.2.2.1).1
    omega
  · -- D6 era_and_sweep: target = M((b+1)::L') (a+4) [1]. ΔΦ = +4.
    subst hcfg; subst htgt
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil]
    omega
  · -- D7 era_and_sweep_solo: target = M [1] (a+4) [1]. ΔΦ = +4.
    subst hcfg; subst htgt
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil]
    omega
  · -- D8 zero_two_solo: target = M L' (a+3) [1]. ΔΦ = +2.
    subst hcfg; subst htgt
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil]
    omega
  · -- D9 zero_bounce_to_zero: target = M0, contradicts hcfg' = M.
    exfalso; subst htgt; injection hcfg'
  · -- D10 zero_bounce_and_shift: target R = [1, 1], length 2 ≠ [1].
    exfalso
    subst htgt
    injection hcfg' with _ _ hR_eq
    injection hR_eq with _ hR'_eq
    exact (List.cons_ne_nil _ _) hR'_eq
  · -- D11 zero_bounce: target = M ((a+4)::L') (z+2) [1]. ΔΦ = +2.
    subst hcfg; subst htgt
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil]
    omega
  · -- D12 zero_two: target R = (d+1)::R'; for R=[1] need d=0, invariant violation.
    exfalso
    subst htgt
    injection hcfg' with _ _ hR_eq
    injection hR_eq with hd_eq _
    subst hcfg
    -- Predecessor cfg has R = 2::d::R'; AllGe1 R gives d ≥ 1.
    have hd_inv := (AllGe1_cons.mp (AllGe1_cons.mp hinv.2.1).2).1
    omega

-- ============================================================
-- A1.2: orbit-reachable era-shape has Φ-strict predecessor (or is init)
-- ============================================================

/-- **A1.2**: every orbit-reachable era-shape config (`M(L, c, [1])`)
    is either the initial config `M([1], 4, [1])` or has an
    orbit-reachable predecessor with `Φ + 2 ≤ cfg.phi`. The Φ-strict
    predecessor witnesses come from:
    - `step_macro`: A1.1 (`macroStep_to_era_shape_phi_strict`).
    - `step_multi_bounce_general`: `phi_macro_multi_bounce_general`
      (ΔΦ = +2 in `phi.lean`).
    - Other multi_bounce / R2 constructors: outputs have `|R| ≥ 2`,
      contradicting era-shape.
    - `step_multi_bounce_general_to_zero`: output is M0, contradicting
      era-shape M.

    `step_R3` was closed (2026-05-05) via the Φ side condition added to
    the constructor: `cfg'.phi = pred.phi + 2`, provided by
    `thm_reach_multi_bounce_last_2_long_safe`'s refactored signature.

    One case retains `sorry`:
    - **`step_R1`**: cfg' is the R1 axiom's witness, unconstrained.
      Closing this case needs joint reasoning with `not_R1` (the
      predecessor `M([], 3, _)` is the very shape we're excluding —
      handled in stage F via mutual induction or `not_R1` upstream). -/
theorem OrbitReachable.era_shape_phi_strict_predecessor
    {cfg : MacroConfig} (h : OrbitReachable cfg)
    {L : List Nat} {c : Nat} (hcfg : cfg = .M L c [1]) :
    cfg = .M [1] 4 [1] ∨
    ∃ cfg_pre, OrbitReachable cfg_pre ∧ cfg_pre.phi + 2 ≤ cfg.phi := by
  induction h with
  | init => exact Or.inl rfl
  | step_macro h_prev h_step _ =>
    refine Or.inr ⟨_, h_prev, ?_⟩
    exact macroStep_to_era_shape_phi_strict h_prev.macroInvariant h_step hcfg
  | step_multi_bounce_general h_prev _ =>
    refine Or.inr ⟨_, h_prev, ?_⟩
    -- Expand Φ on both sides; arithmetic closes ΔΦ = +2 (from
    -- `phi_macro_multi_bounce_general` modulo definitional reformulation).
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_append,
               List.sum_cons, List.sum_nil, List.sum_reverse]
    omega
  | step_multi_bounce_general_to_zero _ _ =>
    -- Output is M0, contradicting hcfg : cfg = M (...) (...) [1].
    exfalso; injection hcfg
  | step_multi_bounce_2_and_shift _ _ =>
    -- Output R = [1, 1], length 2 ≠ [1].
    exfalso
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_multi_bounce_2_double_shift _ _ =>
    exfalso
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_multi_bounce_3run_last_2 _ _ =>
    exfalso
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_multi_bounce_last_2_general _ _ =>
    exfalso
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_R2_zero _ _ =>
    -- Output R = [1, 1, 1, 1].
    exfalso
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_R2_succ _ _ =>
    -- Output R = [1, 1, 1].
    exfalso
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_R3 h_prev _ _ _ _ _ h_phi _ =>
    -- Closed via the new Φ side condition `h_phi : cfg'.phi = pred.phi + 2`.
    -- Take pred (= the M0 predecessor) as the Φ-strict witness.
    refine Or.inr ⟨_, h_prev, ?_⟩
    omega
  | step_R1 h_pred _ _ _ h_phi =>
    -- Φ side condition: cfg'.phi ≥ predecessor.phi + 2.
    -- Predecessor is M([], 3, d::R'), so its Φ = 3 + d + R'.sum + 0 (L=[]).
    -- Take the predecessor as the Φ-strict witness.
    refine Or.inr ⟨_, h_pred, ?_⟩
    simp only [MacroConfig.phi_M, List.sum_nil] at h_phi ⊢
    omega

-- ============================================================
-- A2.0: universal Φ ≥ 6 invariant on OrbitReachable
-- ============================================================

/-- **A2.0**: every orbit-reachable config has Φ ≥ 6. The bound is tight at
    `init` (Φ = 6) and grows by +2 per `step_multi_bounce_*` / `step_R2_*`
    application. The `step_macro` case is the only one where Φ might stay
    constant (sweep family Δ=0); the IH carries the bound through.

    `step_R3` was closed (2026-05-05) via the new Φ side condition on
    the constructor: cfg'.phi = predecessor.phi + 2. Combined with the
    IH (predecessor.phi ≥ 6), gives cfg'.phi ≥ 8 ≥ 6.

    One case retains `sorry`:
    - **`step_R1`**: cfg' is the R1-axiom witness; Φ unconstrained
      abstractly. In `not_R1` proofs, this case is vacuous (predecessor
      M([], 3, _) is itself the excluded shape). For the standalone Φ
      lemma, deferred. -/
theorem OrbitReachable.phi_ge_init {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg.phi ≥ 6 := by
  induction h with
  | init =>
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
    omega
  | step_macro _ h_step ih =>
    have h := macroStep_phi_nondec _ _ _ h_step
    omega
  | step_multi_bounce_general _ _ =>
    simp only [MacroConfig.phi_M, List.sum_append, List.sum_cons,
               List.sum_nil, List.sum_reverse]
    omega
  | step_multi_bounce_general_to_zero _ _ =>
    simp only [MacroConfig.phi_M0, List.sum_append, List.sum_cons,
               List.sum_nil, List.sum_reverse]
    omega
  | step_multi_bounce_2_and_shift _ _ =>
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
    omega
  | step_multi_bounce_2_double_shift _ _ =>
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
    omega
  | step_multi_bounce_3run_last_2 _ _ =>
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
    omega
  | step_multi_bounce_last_2_general _ _ =>
    simp only [MacroConfig.phi_M, List.sum_append, List.sum_cons,
               List.sum_nil, List.sum_reverse]
    omega
  | step_R2_zero _ _ =>
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
    omega
  | step_R2_succ _ _ =>
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil]
    omega
  | step_R3 _ _ _ _ _ _ h_phi ih =>
    -- IH: pred.phi ≥ 6. h_phi: cfg'.phi = pred.phi + 2 ≥ 8 ≥ 6. omega closes.
    omega
  | step_R1 _ _ _ _ h_phi ih =>
    -- IH: predecessor.phi ≥ 6. h_phi: cfg'.phi ≥ predecessor.phi + 2 ≥ 8 ≥ 6.
    simp only [MacroConfig.phi_M, List.sum_nil] at h_phi ih
    omega

-- ============================================================
-- A2.1: Φ < 6 corollaries — small-Φ shapes are unreachable
-- ============================================================

/-- **A2.1**: any config with Φ < 6 is not orbit-reachable. Direct
    contrapositive of `OrbitReachable.phi_ge_init`. -/
theorem OrbitReachable.not_phi_lt_six {cfg : MacroConfig}
    (h_phi : cfg.phi < 6) : ¬ OrbitReachable cfg := by
  intro h
  have := h.phi_ge_init
  omega

/-- M0([2], [1]) is not orbit-reachable: Φ = 3 < 6.
    Building block for Stage B (M([1], 5, [1]) era-start exclusion):
    M([1], 5, [1]) is reached via era_and_sweep_solo (D7) only from
    M0([2], [1]), which this lemma rules out. -/
theorem OrbitReachable.not_M0_2_1 :
    ¬ OrbitReachable (.M0 [2] [1]) := by
  refine OrbitReachable.not_phi_lt_six ?_
  simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
  omega

/-- M0([2, 1], [2]) is not orbit-reachable: Φ = 5 < 6.
    Building block for Stage B: M([1], 5, [1]) is reached via
    zero_two_solo (D8) only from M0([2, 1], [2]), which this lemma
    rules out (alongside `not_M0_2_1`). -/
theorem OrbitReachable.not_M0_2_1_2 :
    ¬ OrbitReachable (.M0 [2, 1] [2]) := by
  refine OrbitReachable.not_phi_lt_six ?_
  simp only [MacroConfig.phi_M0, List.sum_cons, List.sum_nil]
  omega

-- ============================================================
-- BadShape predicate: cascade closure of M([], 3, R) under macroStep predecessors
-- ============================================================
-- `BadShape cfg` means: cfg's forward macroStep trajectory eventually
-- reaches some `M([], 3, R)` shape (i.e., R1-trigger). By construction,
-- BadShape is closed under macroStep predecessors.
--
-- Goal: `OrbitReachable cfg → ¬ BadShape cfg`. By induction on
-- OrbitReachable, this closes the multi-R case of
-- `OrbitReachable.not_M_empty_3` from `era.lean`.

/-- BadShape: closure of `M([], 3, R)` under `macroStep` predecessors.

    `BadShape cfg` iff cfg's forward `macroStep` trajectory ever reaches
    some `M([], 3, R)`. By cascade analysis, this corresponds to cfg
    being in the predecessor cone of the R1-trigger shape. -/
inductive BadShape : MacroConfig → Prop where
  | base (R : List Nat) : BadShape (.M [] 3 R)
  | step {cfg cfg' : MacroConfig} {k : Nat} :
      BadShape cfg' → macroStep cfg = some (k, cfg') → BadShape cfg

/-- Inversion lemma: extract BadShape's structure without dependent
    elimination on cfg's specific form. -/
theorem BadShape.cases_form {cfg : MacroConfig} (h : BadShape cfg) :
    (∃ R, cfg = .M [] 3 R) ∨
    (∃ (k : Nat) (cfg' : MacroConfig), macroStep cfg = some (k, cfg') ∧ BadShape cfg') := by
  cases h with
  | base R => exact Or.inl ⟨R, rfl⟩
  | step h_bad' h_step => exact Or.inr ⟨_, _, h_step, h_bad'⟩

/-- **R1-shape Φ-pruning** (Sub-plan C-3 partial closure, 2026-05-06):
    `M([], 3, R)` with `R.sum < 3` is not orbit-reachable.
    Φ(M([], 3, R)) = 0 + R.sum + 3 = R.sum + 3 < 6, contradicting
    `phi_ge_init`.

    Excludes:
    - `M([], 3, [1])`        (Φ = 4)
    - `M([], 3, [2])`        (Φ = 5)
    - `M([], 3, [1, 1])`     (Φ = 5)

    Other R values (`R.sum ≥ 3`) are NOT excluded by Φ alone and
    require the cascade closure documented in
    `plan-era-graded-not_R1.md` Sub-plan C analysis (≥ 600 lines of
    well-founded induction infrastructure). -/
theorem OrbitReachable.not_M_empty_3_low_R_sum (R : List Nat)
    (h_sum : R.sum < 3) :
    ¬ OrbitReachable (.M [] 3 R) := by
  refine OrbitReachable.not_phi_lt_six ?_
  simp only [MacroConfig.phi_M, List.sum_nil]
  omega

-- ============================================================
-- Stage B: M([1], 5, [1]) excluded from OrbitReachable
-- ============================================================

/-- **Stage B**: M([1], 5, [1]) is not orbit-reachable.

    By A1.1 + A2.0 (Φ-strict predecessor argument):
    M([1], 5, [1]) has Φ = 7. Any `step_macro` predecessor has
    Φ ≤ 7 - 2 = 5 (A1.1), but every orbit-reachable config has
    Φ ≥ 6 (A2.0). Contradiction.

    By output-shape mismatch:
    - `init` has cursor 4 ≠ 5.
    - All multi_bounce / R2 constructors produce outputs whose
      L (≥ 2 elements) or R (≥ 2 elements) doesn't match [1] / [1].

    `step_R3` was closed (2026-05-05) via the constructor's Φ side
    condition + structural Φ lower bound. `step_R1` retains a sorry,
    closed via mutual induction with `not_R1` (upstream).

    This is the Stage B → Stage C lift: combined with the structural
    fact (only era-start M([1], 5, [1]) intra-era reaches M([], 3, _)),
    this is the key lemma for closing R1. -/
theorem OrbitReachable.not_M_1_5_1 {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M [1] 5 [1] := by
  induction h with
  | init =>
    intro hcfg
    injection hcfg with _ hc _
    omega
  | step_macro h_prev h_step _ =>
    intro hcfg
    -- A1.1: pred.phi + 2 ≤ cfg.phi = 7, so pred.phi ≤ 5.
    -- A2.0: pred.phi ≥ 6. Contradiction.
    have h1 := macroStep_to_era_shape_phi_strict h_prev.macroInvariant h_step hcfg
    have h2 := h_prev.phi_ge_init
    rw [hcfg] at h1
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h1
    omega
  | step_multi_bounce_general _ _ =>
    -- Output L = R_mid.reverse ++ (r'+1) :: (a+4) :: L' has length ≥ 2.
    intro hcfg
    injection hcfg with hL _ _
    have h_len := congr_arg List.length hL
    simp at h_len
    omega
  | step_multi_bounce_general_to_zero _ _ =>
    -- Output is M0, not M.
    intro hcfg; injection hcfg
  | step_multi_bounce_2_and_shift _ _ =>
    -- Output R = [1, 1], not [1].
    intro hcfg
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_multi_bounce_2_double_shift _ _ =>
    intro hcfg
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_multi_bounce_3run_last_2 _ _ =>
    intro hcfg
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_multi_bounce_last_2_general _ _ =>
    intro hcfg
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_R2_zero _ _ =>
    -- Output R = [1, 1, 1, 1].
    intro hcfg
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_R2_succ _ _ =>
    -- Output R = [1, 1, 1].
    intro hcfg
    injection hcfg with _ _ hR
    injection hR with _ hR2
    exact List.cons_ne_nil _ _ hR2
  | step_R3 _ _ _ _ _ _ h_phi _ =>
    -- h_phi: cfg'.phi = pred.phi + 2. Φ(M [1] 5 [1]) = 7 < pred.phi + 2 (since
    -- pred.phi ≥ 0 + 6 = 6 from the M0 shape's structural arithmetic, so
    -- pred.phi + 2 ≥ 8 ≠ 7). Contradiction.
    intro hcfg
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0, List.sum_append,
               List.sum_cons, List.sum_nil] at h_phi
    omega
  | step_R1 h_pred _ _ _ h_phi _ =>
    -- h_phi: cfg'.phi ≥ predecessor.phi + 2. Predecessor M([], 3, d::R')
    -- has phi ≥ 6 (from h_pred.phi_ge_init), so cfg'.phi ≥ 8.
    -- M([1], 5, [1]).phi = 7 < 8. Contradiction.
    intro hcfg
    rw [hcfg] at h_phi
    have h_pre := h_pred.phi_ge_init
    simp only [MacroConfig.phi_M, List.sum_cons, List.sum_nil] at h_phi h_pre
    omega

-- ============================================================
-- OrbitReachable.not_BadShape: the cascade closure
-- ============================================================

/-- **Cascade closure** (Sub-plan C-3, Option A, 2026-05-06): BadShape cfg
    implies cfg is not orbit-reachable. By structural induction on h_bad:
    - `step h_bad' h_step`: by IH, ¬ OrbitReachable cfg'. Forward
      extension via `h_or.step_macro h_step` produces OrbitReachable cfg',
      contradicting IH. ✓
    - `base R`: cfg = M([], 3, R). Need ¬ OrbitReachable cfg. The
      residual cascade-closure goal (sole `sorry`). -/
theorem BadShape.not_OrbitReachable {cfg : MacroConfig}
    (h_bad : BadShape cfg) : ¬ OrbitReachable cfg := by
  induction h_bad with
  | base R =>
    intro _
    -- ¬ OrbitReachable (M [] 3 R). Original cascade-closure goal.
    sorry
  | step h_bad' h_step ih =>
    intro h_or
    -- ih : ¬ OrbitReachable cfg'. Build OrbitReachable cfg' via step_macro.
    exact ih (h_or.step_macro h_step)

/-- Original direction: corollary of `BadShape.not_OrbitReachable`. -/
theorem OrbitReachable.not_BadShape {cfg : MacroConfig}
    (h : OrbitReachable cfg) (h_bad : BadShape cfg) : False :=
  h_bad.not_OrbitReachable h

/-- **Corollary**: combining `BadShape.base` with `not_BadShape` closes
    the R1-shape exclusion for orbit-reachable configs. -/
theorem OrbitReachable.not_M_empty_3_full {cfg : MacroConfig}
    (h : OrbitReachable cfg) : ∀ R, cfg ≠ .M [] 3 R := by
  intro R hcfg
  apply h.not_BadShape
  rw [hcfg]
  exact BadShape.base R

end Sweeper
