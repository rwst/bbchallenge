/-
**Cascade tactic library** (2026-05-07) — automates the high-frequency
boilerplate that recurs ~hundreds of times across `era_orbit_cascade*.lean`.

Quantitative survey of patterns in the cascade files (5631 total lines):

  Pattern                                              Occurrences
  ---------------------------------------------------- -----------
  `exact MacroConfig.noConfusion ...`                  ~378
  `rcases macroStep_eq_some_cases _ _ _ h_step with`   ~46
  `obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩`           ~28
  `have h_pred_phi := h_pred.phi_ge_init`              ~20
  `injection htgt with ...`                            ~hundreds
  `refine OrbitReachable.not_phi_lt_six ?_`            (many)

The tactics here factor those out. Imported by
`era_orbit_cascade.lean` (via `import era_orbit_macros` after this file
is added to the build). To keep the existing `phase2`/`progress`
namespace tactics (`ms_simp`, `ms_done`, `ms_kill`, `ms_inj`,
`ms_inj_all`, `ms_close`) usable, this file imports `era_orbit_2adic`
(transitively pulling in `phase2` and `progress`). The cascade-specific
tactics below all use the `mc_` (macro-cascade) prefix to avoid clashes.

## Tactic API

**Atomic shape-mismatch closers** (work on a named shape-equation hypothesis):

  - `mc_noconf h`
        Close goal via `MacroConfig.noConfusion h`. For h of the form
        `MacroConfig.M ... = MacroConfig.M0 ...` (or symmetric).

  - `mc_inj_omega at h`
        Run `simp only [MacroConfig.M.injEq, MacroConfig.M0.injEq,
        List.cons.injEq] at h` and close by `omega`. For h of shape
        `M0 (a+1) :: L' = M0 [1] (...)` where omega can derive ⊥ from
        the cursor or list-head equation.

  - `mc_inj_simp at h`
        Same simp set without omega — for cases where you want to
        destructure the injectivity result manually.

**Composite D-bullet closers** (close one of the 12 bullets after
`rcases macroStep_eq_some_cases`):

  - `mc_dcase_close`
        Try the standard ladder: `noConfusion htgt`, then
        `mc_inj_omega at htgt`, then `simp_all`-with-injectivity. Closes
        the vast majority of non-productive D-bullets in one line.
        Assumes the bullet's equation is named `htgt`.

**Non-step_macro-rule closers** (the `step_multi_bounce_*`, `step_R2_*`
trailing cases):

  - `mc_rule_close`
        For a rule case where the output's static shape mismatches our
        target. Tries `MacroConfig.noConfusion hcfg`, then
        `MacroConfig.M.injEq` rewrite + standard list-cons reasoning.

**phi-based closers**:

  - `mc_phi_lt_six`
        Close `¬ OrbitReachable cfg` when `cfg.phi < 6`, given `hcfg`.
        Expands to `refine OrbitReachable.not_phi_lt_six ?_ h_or` plus
        `simp only [phi_M, phi_M0, List.sum_cons, List.sum_nil]` plus
        `omega`. Assumes `h_or : OrbitReachable cfg` is in scope.

  - `mc_R1_self`
        Self-contained step_R1 closure: `cfg.phi ≤ 7` ⇒ pred.phi ≥ 6
        from `phi_ge_init` plus h_phi gives ⊥. Assumes hypothesis
        names `h_pred`, `h_phi`, `hcfg` (the standard `cases h_or`
        binding).

  - `mc_R1_callback`
        Callback-style step_R1 closure via `h_excl_R1_pred`. Assumes
        names `h_pred`, `h_phi`, `hcfg`, `h_excl_R1_pred`.

**step_R3 unpacker**:

  - `mc_R3_extract`
        Performs `obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ :=
        h_strict_safe` then `rw [hcfg_M] at hcfg`. Assumes name
        `h_strict_safe`. Leaves the user with `h_disj` unprocessed.
-/

import era_orbit_2adic

namespace Sweeper

open BusyLean

-- ============================================================
-- Atomic shape-mismatch closers
-- ============================================================

/-- `mc_noconf h`: close a goal via `MacroConfig.noConfusion h` for an
    M-vs-M0 shape mismatch. -/
syntax (name := mc_noconf) "mc_noconf " term : tactic
macro_rules
  | `(tactic| mc_noconf $h:term) => `(tactic| exact MacroConfig.noConfusion $h)

/-- `mc_inj_omega at h`: rewrite `MacroConfig` and `List.cons` injectivity
    in `h`, then close via `omega`. -/
syntax (name := mc_inj_omega_loc) "mc_inj_omega" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| mc_inj_omega $l:location) =>
    `(tactic| (simp only [MacroConfig.M.injEq, MacroConfig.M0.injEq,
                          List.cons.injEq] $l:location
               omega))

/-- `mc_inj_simp at h`: rewrite `MacroConfig` and `List.cons` injectivity
    in `h` without trying `omega`. -/
syntax (name := mc_inj_simp_loc) "mc_inj_simp" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| mc_inj_simp $l:location) =>
    `(tactic| simp only [MacroConfig.M.injEq, MacroConfig.M0.injEq,
                         List.cons.injEq] $l:location)

-- ============================================================
-- Composite D-bullet closer
-- ============================================================

-- `mc_dcase_close`: ladder of shape-mismatch tactics for hypothesis
-- `htgt`. Closes non-productive bullets after `rcases macroStep_eq_some_cases`.
-- Strategy: try `noConfusion htgt` first (closes M-vs-M0 mismatches in
-- one step), else aggressively `simp_all` with injectivity lemmas (closes
-- list-cons-vs-nil and trivially-false numeric mismatches), else `omega`
-- to dispatch surviving arithmetic contradictions.
set_option hygiene false in
macro "mc_dcase_close" : tactic =>
  `(tactic| (first
    -- Path A: M-vs-M0 mismatch
    | exact MacroConfig.noConfusion htgt
    -- Path B: both .M, extract 3 components.
    | (rw [MacroConfig.M.injEq] at htgt
       obtain ⟨hL_d, hc_d, hR_d⟩ := htgt
       first
       | omega
       | (rw [List.cons.injEq] at hL_d
          first | omega
                | exact (List.cons_ne_nil _ _) hL_d.2.symm
                | exact (List.cons_ne_nil _ _) hL_d.2)
       | (rw [List.cons.injEq] at hR_d
          first | omega
                | exact (List.cons_ne_nil _ _) hR_d.2.symm
                | exact (List.cons_ne_nil _ _) hR_d.2)
       | (simp only [List.cons.injEq] at hL_d; omega)
       | (simp only [List.cons.injEq] at hR_d; omega)
       | (simp at hL_d)
       | (simp at hR_d)
       | exact (List.cons_ne_nil _ _) hL_d.symm
       | exact (List.cons_ne_nil _ _) hL_d
       | exact (List.cons_ne_nil _ _) hR_d.symm
       | exact (List.cons_ne_nil _ _) hR_d)
    -- Path C: both .M0, extract 2 components
    | (rw [MacroConfig.M0.injEq] at htgt
       obtain ⟨hL_d, hR_d⟩ := htgt
       first
       | (rw [List.cons.injEq] at hL_d
          first | omega
                | exact (List.cons_ne_nil _ _) hL_d.2.symm
                | exact (List.cons_ne_nil _ _) hL_d.2)
       | (rw [List.cons.injEq] at hR_d
          first | omega
                | exact (List.cons_ne_nil _ _) hR_d.2.symm
                | exact (List.cons_ne_nil _ _) hR_d.2)
       | (simp only [List.cons.injEq] at hL_d; omega)
       | (simp only [List.cons.injEq] at hR_d; omega)
       | (simp at hL_d)
       | (simp at hR_d)
       | exact (List.cons_ne_nil _ _) hL_d.symm
       | exact (List.cons_ne_nil _ _) hL_d
       | exact (List.cons_ne_nil _ _) hR_d.symm
       | exact (List.cons_ne_nil _ _) hR_d)))

-- ============================================================
-- Non-step_macro rule closer
-- ============================================================

-- `mc_rule_close`: closer for rule cases (`step_multi_bounce_*`, `step_R2_*`)
-- where the rule's output shape mismatches `cfg`. Assumes name `hcfg`.
-- Mirrors `mc_dcase_close` but operates on `hcfg` (the cfg-shape eq).
set_option hygiene false in
macro "mc_rule_close" : tactic =>
  `(tactic| (first
    | exact MacroConfig.noConfusion hcfg
    | (rw [MacroConfig.M.injEq] at hcfg
       obtain ⟨hL_r, hc_r, hR_r⟩ := hcfg
       first
       | omega
       | (rw [List.cons.injEq] at hL_r
          first | omega
                | exact (List.cons_ne_nil _ _) hL_r.2.symm
                | exact (List.cons_ne_nil _ _) hL_r.2)
       | (rw [List.cons.injEq] at hR_r
          first | omega
                | exact (List.cons_ne_nil _ _) hR_r.2.symm
                | exact (List.cons_ne_nil _ _) hR_r.2)
       | (simp only [List.cons.injEq] at hL_r; omega)
       | (simp only [List.cons.injEq] at hR_r; omega)
       | (simp at hL_r)
       | (simp at hR_r)
       | exact (List.cons_ne_nil _ _) hL_r.symm
       | exact (List.cons_ne_nil _ _) hL_r
       | exact (List.cons_ne_nil _ _) hR_r.symm
       | exact (List.cons_ne_nil _ _) hR_r)
    | (rw [MacroConfig.M0.injEq] at hcfg
       obtain ⟨hL_r, hR_r⟩ := hcfg
       first
       | (rw [List.cons.injEq] at hL_r
          first | omega
                | exact (List.cons_ne_nil _ _) hL_r.2.symm
                | exact (List.cons_ne_nil _ _) hL_r.2)
       | (rw [List.cons.injEq] at hR_r
          first | omega
                | exact (List.cons_ne_nil _ _) hR_r.2.symm
                | exact (List.cons_ne_nil _ _) hR_r.2)
       | (simp only [List.cons.injEq] at hL_r; omega)
       | (simp only [List.cons.injEq] at hR_r; omega)
       | (simp at hL_r)
       | (simp at hR_r)
       | exact (List.cons_ne_nil _ _) hL_r.symm
       | exact (List.cons_ne_nil _ _) hL_r
       | exact (List.cons_ne_nil _ _) hR_r.symm
       | exact (List.cons_ne_nil _ _) hR_r)))

-- ============================================================
-- phi-based closers
-- ============================================================

-- `mc_phi_lt_six`: close `¬ OrbitReachable cfg` when `cfg.phi < 6`.
-- Assumes `h_or : OrbitReachable cfg` is in scope after `intro h_or; rw [hcfg] at h_or`.
set_option hygiene false in
macro "mc_phi_lt_six" : tactic =>
  `(tactic| (
    refine OrbitReachable.not_phi_lt_six ?_ h_or
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil, List.sum_append]
    omega))

-- `mc_R1_self`: step_R1 self-contained closure (cfg.phi ≤ 7 gives ⊥ via phi_ge_init).
-- Names assumed: `h_pred`, `h_phi`, `hcfg`.
set_option hygiene false in
macro "mc_R1_self" : tactic =>
  `(tactic| (
    have h_pred_phi := h_pred.phi_ge_init
    rw [hcfg] at h_phi
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil, List.sum_append] at h_phi h_pred_phi
    omega))

-- `mc_R1_callback`: step_R1 closure via `h_excl_R1_pred` on the predecessor.
-- Names assumed: `h_pred`, `h_phi`, `hcfg`, `h_excl_R1_pred`.
-- The `rw [hcfg]` on the goal is required because the goal has form
-- `… < cfg.phi` where cfg is the outer-bound free variable; simp can't
-- unfold `cfg.phi` until cfg is replaced with its concrete shape.
set_option hygiene false in
macro "mc_R1_callback" : tactic =>
  `(tactic| (
    apply h_excl_R1_pred h_pred
    rw [hcfg] at h_phi
    rw [hcfg]
    simp only [MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_cons, List.sum_nil, List.sum_append] at h_phi ⊢
    omega))

-- ============================================================
-- AllGe1 invariant closers
-- ============================================================

-- `mc_AllGe1_a_ge1`: close via `h_prev`'s AllGe1 invariant on L,
-- giving `a ≥ 1` to contradict `a = 0` (or similar) already in scope.
-- Assumes `h_prev : OrbitReachable cfg_prev` of M-shape and that `omega`
-- can finish from `a_ge` plus the existing hypotheses.
set_option hygiene false in
macro "mc_AllGe1_a_ge1" : tactic =>
  `(tactic| (
    have hAL := h_prev.macroInvariant.1
    have ha_ge := (AllGe1_cons.mp hAL).1
    omega))

-- ============================================================
-- step_R3 unpacker
-- ============================================================

-- `mc_R3_extract`: open `h_strict_safe`'s existential, rewrite into `hcfg`.
-- After this, `h_disj`, `L_suf`, `v`, `R_out` are in scope.
set_option hygiene false in
macro "mc_R3_extract" : tactic =>
  `(tactic| (
    obtain ⟨L_suf, v, R_out, hcfg_M, h_disj⟩ := h_strict_safe
    rw [hcfg_M] at hcfg))

end Sweeper
