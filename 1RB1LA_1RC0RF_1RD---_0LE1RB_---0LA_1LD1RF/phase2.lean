/-
Phase 2: Closing the 3 reachability axioms (R1, R2, R3-narrowed) via
backward analysis on the `OrbitReachable` inductive predicate.

This file is self-contained for Phase 2 work — `machine.lean` provides the
foundation (transition theorems, OrbitReachable definition, OrbitProg).
All new lemmas live here.

The TODO list is in `LOG.md`. This file follows that structure.
-/

import progress

namespace Sweeper

open BusyLean

-- ============================================================
-- Phase 2 tactic macros
-- ============================================================
-- Reduce boilerplate in cascade lemmas. Each shape's backward analysis
-- repeats the same simp pattern dozens of times; macros below make it
-- ~7 chars instead of ~80.
--
-- `ms_simp` and `ms_done` are defined in `progress.lean` alongside `macroStep`,
-- since `macroStep_sound` uses them. This file inherits them via `import progress`.

/-- `ms_kill` discharges the current goal by aggressively reducing all
    hypotheses (including h) using `simp_all [macroStep, ...]` with ctor
    injectivity. Handles M ≠ M0 mismatches that `ms_done` may miss. -/
macro "ms_kill" : tactic =>
  `(tactic| simp_all [macroStep, MacroConfig.M.injEq, MacroConfig.M0.injEq,
                      List.cons.injEq])

/-- `ms_inj at h` applies the standard `MacroConfig.M.injEq`/`MacroConfig.M0.injEq`/
    `List.cons.injEq` simp set to break a target-shape equation in `h`. Used
    in cascade-lemma productive cases after `rcases macroStep_eq_some_cases`. -/
syntax (name := ms_inj_tac) "ms_inj" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| ms_inj $l:location) =>
    `(tactic| simp only [MacroConfig.M.injEq, MacroConfig.M0.injEq,
                         List.cons.injEq] $l:location)

/-- `ms_inj_all` runs `simp_all` with the same set, plus default simp lemmas
    (which discriminate `M ≠ M0` etc. via `noConfusion`). Used in cascade-lemma
    contradiction bullets. -/
macro "ms_inj_all" : tactic =>
  `(tactic| simp_all [MacroConfig.M.injEq, MacroConfig.M0.injEq, List.cons.injEq])

-- `ms_close` is the unified contradiction-closer for the trailing
-- `all_goals` block in cascade lemmas. Tries: (1) `simp_all` with the
-- standard injectivity set; (2) `subst hcfg; <invariant on a from hinv>;
-- omega` (covers `a ≥ 1` cases); (3) `subst hcfg; omega` (pure arithmetic).
-- Requires hypotheses named `hcfg`, `hinv`, `htgt` to be in scope.
-- `hygiene false` is needed so the macro's identifier references resolve
-- against the user's hypotheses rather than fresh hygienic names.
set_option hygiene false in
macro "ms_close" : tactic =>
  `(tactic| all_goals (first
    | (ms_inj_all; done)
    | (subst hcfg
       have ha_local := (AllGe1_cons.mp hinv.1).1
       ms_inj at htgt
       omega)
    | (subst hcfg
       ms_inj at htgt
       omega)))

-- ============================================================
-- Master case-split for macroStep
-- ============================================================
-- Single normalization theorem: every productive `macroStep` result is one of
-- 12 enumerated forms (5 M-side + 7 M0-side). Cascade lemmas use this instead
-- of re-walking the full dispatch tree.

/-- Every productive `macroStep cfg = some (k, target)` matches one of 12
    enumerated forms. Each disjunct fixes `cfg`, `k`, and `target` modulo
    existential parameters (a, c', d, L', R', etc.). -/
theorem macroStep_eq_some_cases (cfg : MacroConfig) (k : Nat) (target : MacroConfig)
    (h : macroStep cfg = some (k, target)) :
    -- M-side (5 productive forms)
    (∃ a L' d R',     cfg = .M (a :: L') 2 (d :: R')      ∧ k = 11
                  ∧ target = .M0 ((a + 1) :: L') ((d + 1) :: R'))
  ∨ (∃ a L' d R',     cfg = .M (a :: L') 3 (d :: R')      ∧ k = 19
                  ∧ target = .M L' (a + 1) (1 :: (d + 1) :: R'))
  ∨ (∃ a c' L' d R',  cfg = .M (a :: L') (c' + 4) (d :: R') ∧ k = 2 * (c' + 4) + 7
                  ∧ target = .M ((a + 1) :: L') (c' + 2) ((d + 1) :: R'))
  ∨ (∃ d R',          cfg = .M [] 2 (d :: R')             ∧ k = 11
                  ∧ target = .M0 [1] ((d + 1) :: R'))
  ∨ (∃ c' d R',       cfg = .M [] (c' + 4) (d :: R')      ∧ k = 2 * (c' + 4) + 7
                  ∧ target = .M [1] (c' + 2) ((d + 1) :: R'))
    -- M0-side (7 productive forms)
  ∨ (∃ a b L',        cfg = .M0 ((a + 1) :: b :: L') [1]  ∧ k = 2 * a + 27
                  ∧ target = .M ((b + 1) :: L') (a + 4) [1])         -- era_and_sweep
  ∨ (∃ a,             cfg = .M0 [a + 1] [1]               ∧ k = 2 * a + 27
                  ∧ target = .M [1] (a + 4) [1])                     -- era_and_sweep_solo
  ∨ (∃ a L',          cfg = .M0 (a :: L') [2]             ∧ k = 8
                  ∧ target = .M L' (a + 3) [1])                      -- zero_two_solo
  ∨ (∃ a L',          cfg = .M0 (a :: L') [3]             ∧ k = 12
                  ∧ target = .M0 ((a + 4) :: L') [1])                -- zero_bounce_to_zero
  ∨ (∃ a L',          cfg = .M0 (a :: L') [4]             ∧ k = 19
                  ∧ target = .M L' (a + 4) [1, 1])                   -- zero_bounce_and_shift
  ∨ (∃ a z L',        cfg = .M0 (a :: L') [z + 5]         ∧ k = z + 1 + 13
                  ∧ target = .M ((a + 4) :: L') (z + 2) [1])         -- zero_bounce
  ∨ (∃ a L' d R',     cfg = .M0 (a :: L') (2 :: d :: R')  ∧ k = 8
                  ∧ target = .M L' (a + 3) ((d + 1) :: R')) := by    -- zero_two
  -- Strategy: case-split cfg to a productive shape, normalize h via
  -- `simp only [macroStep, Option.some.injEq, Prod.mk.injEq]` (NO MacroConfig
  -- injectivity — target is a free variable, so we keep the target equation
  -- whole), then provide the matching disjunct with `hk.symm` and `htgt.symm`.
  cases cfg with
  | M L c R_cfg =>
    cases L with
    | nil =>
      cases R_cfg with
      | nil => simp [macroStep] at h
      | cons d R' =>
        rcases Nat.lt_or_ge c 4 with hc | hc
        · interval_cases c
          · simp [macroStep] at h
          · simp [macroStep] at h
          · -- c = 2: sweep_to_zero_left_empty, k=11, target=M0 [1] ((d+1)::R')
            simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, htgt⟩ := h
            right; right; right; left
            exact ⟨d, R', rfl, hk.symm, htgt.symm⟩
          · simp [macroStep] at h
        · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 4 := ⟨c - 4, by omega⟩
          -- c ≥ 4: sweep_left_empty
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; right; right; left
          exact ⟨c', d, R', rfl, hk.symm, htgt.symm⟩
    | cons a L' =>
      cases R_cfg with
      | nil => simp [macroStep] at h
      | cons d R' =>
        rcases Nat.lt_or_ge c 4 with hc | hc
        · interval_cases c
          · simp [macroStep] at h
          · simp [macroStep] at h
          · -- c = 2: sweep_to_zero
            simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, htgt⟩ := h
            left
            exact ⟨a, L', d, R', rfl, hk.symm, htgt.symm⟩
          · -- c = 3: sweep_and_shift
            simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, htgt⟩ := h
            right; left
            exact ⟨a, L', d, R', rfl, hk.symm, htgt.symm⟩
        · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 4 := ⟨c - 4, by omega⟩
          -- c ≥ 4: sweep
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; left
          exact ⟨a, c', L', d, R', rfl, hk.symm, htgt.symm⟩
  | M0 L R_cfg =>
    cases L with
    | nil => simp [macroStep] at h
    | cons a L' =>
      cases R_cfg with
      | nil => cases L' <;> simp [macroStep] at h
      | cons r R' =>
        -- Split on r: 0, 1, 2, 3, 4, z+5.
        match r, R' with
        | 0, _ => simp [macroStep] at h  -- (_::_, 0::_) → none
        | 1, [] =>
          -- era_and_sweep variants (a≥1) or none (a=0)
          cases a with
          | zero =>
            -- (0 :: _ :: _), [1] → none, or [0], [1] → none
            cases L' <;> simp [macroStep] at h
          | succ a' =>
            cases L' with
            | nil =>
              -- era_and_sweep_solo: M0 [a'+1] [1] → M [1] (a'+4) [1], k=2*a'+27
              simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk, htgt⟩ := h
              right; right; right; right; right; right; left
              exact ⟨a', rfl, hk.symm, htgt.symm⟩
            | cons b L'' =>
              -- era_and_sweep: M0 ((a'+1)::b::L'') [1] → M ((b+1)::L'') (a'+4) [1]
              simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk, htgt⟩ := h
              right; right; right; right; right; left
              exact ⟨a', b, L'', rfl, hk.symm, htgt.symm⟩
        | 1, _ :: _ => simp [macroStep] at h  -- (_::_, 1::_::_) → none
        | 2, [] =>
          -- zero_two_solo: M0 (a::L') [2] → M L' (a+3) [1], k=8
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; right; right; right; right; right; left
          exact ⟨a, L', rfl, hk.symm, htgt.symm⟩
        | 2, d :: R'' =>
          -- zero_two: M0 (a::L') (2::d::R'') → M L' (a+3) ((d+1)::R''), k=8
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; right; right; right; right; right; right; right; right; right
          exact ⟨a, L', d, R'', rfl, hk.symm, htgt.symm⟩
        | 3, [] =>
          -- zero_bounce_to_zero: M0 (a::L') [3] → M0 ((a+4)::L') [1], k=12
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; right; right; right; right; right; right; left
          exact ⟨a, L', rfl, hk.symm, htgt.symm⟩
        | 3, _ :: _ => simp [macroStep] at h  -- multi_bounce → none
        | 4, [] =>
          -- zero_bounce_and_shift: M0 (a::L') [4] → M L' (a+4) [1, 1], k=19
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; right; right; right; right; right; right; right; left
          exact ⟨a, L', rfl, hk.symm, htgt.symm⟩
        | 4, _ :: _ => simp [macroStep] at h
        | z + 5, [] =>
          -- zero_bounce: M0 (a::L') [z+5] → M ((a+4)::L') (z+2) [1], k=z+1+13
          simp only [macroStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, htgt⟩ := h
          right; right; right; right; right; right; right; right; right; right; left
          exact ⟨a, z, L', rfl, hk.symm, htgt.symm⟩
        | z + 5, _ :: _ => simp [macroStep] at h

-- ============================================================
-- Tier 1: trivial corollaries of `OrbitReachable.macroInvariant`
-- ============================================================
-- Every reachable config satisfies MacroInvariant; these lemmas extract
-- specific consequences (R nonempty, no halt pattern, etc.). All proofs
-- are one-liners via `macroInvariant`.

/-- Every orbit-reachable M_Config has nonempty R. -/
theorem OrbitReachable.M_R_nonempty {L R : List Nat} {c : Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M L c R) : R ≠ [] := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.2.2

/-- Every orbit-reachable M0_Config has nonempty R. -/
theorem OrbitReachable.M0_R_nonempty {L R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M0 L R) : R ≠ [] := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.2.2.1

/-- Every orbit-reachable M0_Config satisfies NoHaltPattern (no `1 :: (z+1) :: _` shape). -/
theorem OrbitReachable.M0_no_halt_pattern {L R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M0 L R) : NoHaltPattern R := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.2.2.2

/-- All elements of an orbit-reachable M's R are ≥ 1. -/
theorem OrbitReachable.M_R_AllGe1 {L R : List Nat} {c : Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M L c R) : AllGe1 R := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.2.1

/-- All elements of an orbit-reachable M0's R are ≥ 1. -/
theorem OrbitReachable.M0_R_AllGe1 {L R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M0 L R) : AllGe1 R := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.2.1

/-- All elements of an orbit-reachable M's L are ≥ 1. -/
theorem OrbitReachable.M_L_AllGe1 {L R : List Nat} {c : Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M L c R) : AllGe1 L := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.1

/-- All elements of an orbit-reachable M0's L are ≥ 1. -/
theorem OrbitReachable.M0_L_AllGe1 {L R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) (hcfg : cfg = .M0 L R) : AllGe1 L := by
  have hinv := h.macroInvariant
  rw [hcfg] at hinv
  exact hinv.1

-- ============================================================
-- Tier 2: structural inequalities at `init`
-- ============================================================
-- The init constructor case for any non-reachability theorem reduces to
-- showing the initial config M([1], 4, [1]) doesn't match the axiom shape.
-- Pulled out as a helper to reuse across all cascade lemmas.

/-- The initial config is not M_Config with c = 3. -/
theorem init_ne_M_c3 {L R : List Nat} : (.M [1] 4 [1] : MacroConfig) ≠ .M L 3 R := by
  intro h
  have : (4 : Nat) = 3 := (MacroConfig.M.injEq _ _ _ _ _ _).mp h |>.2.1
  omega

/-- The initial config is not M0_Config. -/
theorem init_ne_M0 {L R : List Nat} : (.M [1] 4 [1] : MacroConfig) ≠ .M0 L R := by
  intro h
  injection h

/-- The initial config is not M_Config with empty L. -/
theorem init_ne_M_empty_L {c : Nat} {R : List Nat} :
    (.M [1] 4 [1] : MacroConfig) ≠ .M [] c R := by
  intro h
  injection h with hL hc hR
  exact List.cons_ne_nil _ _ hL

-- ============================================================
-- Tier 3: R1 closure cascade — helpers
-- ============================================================
-- Top-level: OrbitReachable.not_R1.
-- Helpers (cascade): not_L_head_2_at_c3_M, not_L_head_1_at_c5_M,
--                    not_M0_R_4_3_2, not_M0_R_4_4, etc.

/-- Helper: in the `init` case of OrbitReachable induction, M([1], 4, [1])
    structurally is not at cursor 3. Used as a pattern below. -/
private theorem M_init_ne_M_c3 {a : Nat} {L R : List Nat} :
    (.M [1] 4 [1] : MacroConfig) ≠ .M (a :: L) 3 R := by
  intro h
  injection h with hL hc hR
  omega

/-- Helper: in the `init` case, M([1], 4, [1]) is not M0. -/
private theorem M_init_ne_M0 {L R : List Nat} :
    (.M [1] 4 [1] : MacroConfig) ≠ .M0 L R := by
  intro h
  injection h

-- ============================================================
-- Tier 3a: M0 halt-pattern exclusions (derive from NoHaltPattern)
-- ============================================================
-- These are non-trivial Tier 1 results in disguise — they exclude specific
-- M0 R shapes that violate NoHaltPattern. Useful as building blocks for the
-- multi-step cascade lemmas below.

/-- M0 with R = [1, 2] is unreachable (NoHaltPattern violation). -/
theorem OrbitReachable.not_M0_R_1_2 {L : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M0 L [1, 2] := by
  intro hcfg
  have hNH := h.M0_no_halt_pattern hcfg
  exact hNH 1 [] rfl

/-- M0 with R = 1 :: (z+1) :: R' is unreachable (any R' — the halt-pattern shape). -/
theorem OrbitReachable.not_M0_R_halt_pattern {L : List Nat} {z : Nat} {R' : List Nat}
    {cfg : MacroConfig} (h : OrbitReachable cfg) : cfg ≠ .M0 L (1 :: (z + 1) :: R') := by
  intro hcfg
  have hNH := h.M0_no_halt_pattern hcfg
  exact hNH z R' rfl

-- ============================================================
-- Tier 3b: M0 R[0] = 0 exclusions (derive from AllGe1 R)
-- ============================================================

/-- M0 with R[0] = 0 is unreachable (AllGe1 violation). -/
theorem OrbitReachable.not_M0_R_starts_0 {L R' : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M0 L (0 :: R') := by
  intro hcfg
  have hAllGe1 := h.M0_R_AllGe1 hcfg
  rw [AllGe1_cons] at hAllGe1
  omega

/-- M with R[0] = 0 is unreachable (AllGe1 violation). -/
theorem OrbitReachable.not_M_R_starts_0 {L R' : List Nat} {c : Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M L c (0 :: R') := by
  intro hcfg
  have hAllGe1 := h.M_R_AllGe1 hcfg
  rw [AllGe1_cons] at hAllGe1
  omega

/-- M with empty R is unreachable. -/
theorem OrbitReachable.not_M_R_empty {L : List Nat} {c : Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M L c [] := by
  intro hcfg
  exact h.M_R_nonempty hcfg rfl

/-- M0 with empty R is unreachable. -/
theorem OrbitReachable.not_M0_R_empty {L : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M0 L [] := by
  intro hcfg
  exact h.M0_R_nonempty hcfg rfl

-- ============================================================
-- Tier 3c: cursor-violation exclusions
-- ============================================================

/-- M with cursor 0 is unreachable. -/
theorem OrbitReachable.not_M_c_0 {L R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M L 0 R := by
  intro hcfg
  have := h.M_cursor_ge_2 hcfg
  omega

/-- M with cursor 1 is unreachable. -/
theorem OrbitReachable.not_M_c_1 {L R : List Nat} {cfg : MacroConfig}
    (h : OrbitReachable cfg) : cfg ≠ .M L 1 R := by
  intro hcfg
  have := h.M_cursor_ge_2 hcfg
  omega

-- ============================================================
-- Tier 3d: macroStep dead-ends (M shapes with no macroStep image)
-- ============================================================
-- These lemmas document that certain shapes return `none` from macroStep,
-- meaning the orbit can only reach them via `step_run` (raw TM transitions
-- through macro_progress's axiom branches).

/-- macroStep returns none on M([], 3, R) — the R1 axiom shape. -/
theorem macroStep_M_nil_3_eq_none (R : List Nat) : macroStep (.M [] 3 R) = none := by
  cases R with
  | nil => rfl
  | cons _ _ => rfl

/-- macroStep returns none on M([], c, []) for any c — empty R is invalid. -/
theorem macroStep_M_R_empty_eq_none (L : List Nat) (c : Nat) :
    macroStep (.M L c []) = none := by
  cases L <;> cases c <;> rfl

/-- macroStep returns none on M0([], R) — empty L violates invariant. -/
theorem macroStep_M0_L_empty_eq_none (R : List Nat) : macroStep (.M0 [] R) = none := by
  rfl

/-- macroStep returns none on M0(L, []) — empty R violates invariant. -/
theorem macroStep_M0_R_empty_eq_none (L : List Nat) : macroStep (.M0 L []) = none := by
  cases L <;> rfl

-- ============================================================
-- Tier 3e: structural backward analysis on macroStep (c=3 case)
-- ============================================================
-- Demonstrates the technique: prove that the SPECIFIC predecessor at c=3
-- with multi-element R is exactly M([2], 3, _) modulo extraction.
-- Full enumeration over ALL c values requires MacroInvariant hypothesis
-- (deferred to Tier 3f).

-- ============================================================
-- Tier 3g: top-level R1 backward analysis
-- ============================================================

/-- The unique predecessor (under MacroInvariant) of M([], 3, R) via macroStep
    is M([2], 3, _). All paths through the dispatch table either return none
    or produce different output shapes. -/
theorem macroStep_M_empty_3_predecessor (cfg : MacroConfig) (k : Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [] 3 R)) :
    ∃ d_pre R_pre, cfg = .M [2] 3 (d_pre :: R_pre)
      ∧ R = 1 :: (d_pre + 1) :: R_pre
      ∧ k = 19 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Productive — M (a::L') 3 (d::R'), target M L' (a+1) (1::(d+1)::R') = M [] 3 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    exact ⟨d, R', hcfg, hR_eq, hk⟩
  ms_close

-- ============================================================
-- Tier 3h: partial R1 closure via OrbitReachable induction
-- ============================================================
-- Demonstrates the structural framework — the `init` case of `not_R1`
-- closes immediately. The `step_macro` and `step_run` cases require
-- additional cascade lemmas (excluding M([2], 3, _) etc.).

/-- R1 closure for the `init` constructor case: trivially M([1], 4, [1]) ≠ R1 shape. -/
theorem OrbitReachable.init_ne_R1 {d : Nat} {R' : List Nat} :
    (.M [1] 4 [1] : MacroConfig) ≠ .M [] 3 (d :: R') :=
  init_ne_M_empty_L

-- ============================================================
-- Tier 3i: Layer 1 cascade — backward analysis for M((2 :: _), 3, _)
-- ============================================================
-- Producers of M((2 :: L_tail), 3, R) via macroStep:
-- 1. sweep_and_shift on M(2 :: 2 :: L_tail, 3, _) — SELF-RECURSIVE
-- 2. sweep at c=5 on M(1 :: L_tail, 5, _) — needs L head = 1 at c=5 exclusion

/-- The unique predecessor (under MacroInvariant) of M(2 :: L_out, 3, R) via
    macroStep is either M(2 :: 2 :: L_out, 3, _) (self-recursive) OR
    M(1 :: L_out, 5, _) (sweep at c=5 case).
    All other macroStep paths are excluded. -/
theorem macroStep_M_cons_2_3_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (2 :: L_out) 3 R)) :
    (∃ d R', cfg = .M (2 :: 2 :: L_out) 3 (d :: R') ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    ∨ (∃ d R', cfg = .M (1 :: L_out) 5 (d :: R') ∧ R = (d + 1) :: R' ∧ k = 17) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨a, c', L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 1 — M (a::L') 3 (d::R'), target M L' (a+1) (1::(d+1)::R') = M (2::L_out) 3 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · -- D3: Producer 2 — M (a::L') (c'+4) (d::R'), target M ((a+1)::L') (c'+2) ((d+1)::R')
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hc, hR_eq⟩ := htgt
    have ha1 : a = 1 := by omega
    have hc1 : c' = 1 := by omega
    subst hL'; subst ha1; subst hc1
    right; exact ⟨d, R', hcfg, hR_eq, hk⟩
  ms_close

-- ============================================================
-- Tier 3j: Layer 2 cascade — backward analysis for M((1 :: _), 5, _)
-- ============================================================
-- Producers of M((1 :: L_out), 5, R) via macroStep:
-- M_Config side:
-- 1. sweep_left_empty at c=7 (when L_out = []): M([], 7, _).
-- 2. sweep_and_shift at c=3 with L head = 4: M(4 :: 1 :: L_out, 3, _).
-- 3. sweep at c=7 with L head = 0: invariant violation (excluded by AllGe1).
-- M0_Config side (under MacroInvariant):
-- 4. era_and_sweep_solo (when L_out = []): M0([2], [1]).
-- 5. zero_two_solo: M0(2 :: 1 :: L_out, [2]).
-- 6. zero_two: M0(2 :: 1 :: L_out, [2, d, R']).
-- 7. zero_bounce_and_shift (when R = [1, 1]): M0(1 :: 1 :: L_out, [4]).

-- ============================================================
-- Layer 3 Shape 2: M(4 :: 1 :: L_out, 3, _)
-- ============================================================

/-- Layer 3 Shape 2 backward analysis: under MacroInvariant, the macroStep
    predecessors of M(4 :: 1 :: L_out, 3, R) are exactly:
    1. M(2 :: 4 :: 1 :: L_out, 3, _) via sweep_and_shift (k=19)
    2. M(3 :: 1 :: L_out, 5, _) via sweep at c=5 (k=17). -/
theorem macroStep_M_cons_4_1_3_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (4 :: 1 :: L_out) 3 R)) :
    (∃ d R', cfg = .M (2 :: 4 :: 1 :: L_out) 3 (d :: R')
        ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    ∨ (∃ d R', cfg = .M (3 :: 1 :: L_out) 5 (d :: R')
        ∧ R = (d + 1) :: R' ∧ k = 17) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨a, c', L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 1 — M (a::L') 3 (d::R'), target M L' (a+1) (1::(d+1)::R') = M (4::1::L_out) 3 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · -- D3: Producer 2 — M (a::L') (c'+4) (d::R'), target M ((a+1)::L') (c'+2) ((d+1)::R')
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hc, hR_eq⟩ := htgt
    have ha3 : a = 3 := by omega
    have hc1 : c' = 1 := by omega
    subst hL'; subst ha3; subst hc1
    right; exact ⟨d, R', hcfg, hR_eq, hk⟩
  ms_close

-- ============================================================
-- Layer 3 Shape 1: M([], 7, d :: R')
-- ============================================================

/-- Layer 3 Shape 1 backward analysis: under MacroInvariant, the macroStep
    predecessors of M([], 7, R) are exactly 4 producer shapes. -/
theorem macroStep_M_nil_7_predecessor (cfg : MacroConfig) (k : Nat)
    (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [] 7 R)) :
    -- Producer 1: sweep_and_shift on M([6], 3, d :: R')
    (∃ d R', cfg = .M [6] 3 (d :: R') ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    -- Producer 2: zero_two_solo on M0([4], [2])
    ∨ (cfg = .M0 [4] [2] ∧ R = [1] ∧ k = 8)
    -- Producer 3: zero_two on M0([4], 2 :: d :: R')
    ∨ (∃ d R', cfg = .M0 [4] (2 :: d :: R') ∧ R = (d + 1) :: R' ∧ k = 8)
    -- Producer 4: zero_bounce_and_shift on M0([3], [4])
    ∨ (cfg = .M0 [3] [4] ∧ R = [1, 1] ∧ k = 19) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, _, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, _, _, _, htgt⟩
  | ⟨_, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, htgt⟩
  | ⟨_, _, _, htgt⟩
  | ⟨a, L', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, htgt⟩
  | ⟨a, L', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 1 — M (a::L') 3 (d::R') with target M L' (a+1) (1::(d+1)::R') = M [] 7 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha6 : a = 6 := by omega
    subst hL'; subst ha6
    left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D3
  · ms_inj_all  -- D4
  · ms_inj_all  -- D5
  · ms_inj_all  -- D6
  · ms_inj_all  -- D7
  · -- D8: Producer 2 — M0 (a::L') [2] with target M L' (a+3) [1] = M [] 7 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha4 : a = 4 := by omega
    subst hL'; subst ha4
    right; left; exact ⟨hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D9
  · -- D10: Producer 4 — M0 (a::L') [4] with target M L' (a+4) [1,1] = M [] 7 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha3 : a = 3 := by omega
    subst hL'; subst ha3
    right; right; right; exact ⟨hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D11
  · -- D12: Producer 3 — M0 (a::L') (2::d::R') with target M L' (a+3) ((d+1)::R') = M [] 7 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha4 : a = 4 := by omega
    subst hL'; subst ha4
    right; right; left; exact ⟨d, R', hcfg, hR_eq, hk⟩

-- ============================================================
-- Tier 3l: Layer 2 top-level — combined backward analysis
-- ============================================================

/-- Layer 2 backward analysis: under MacroInvariant, the macroStep predecessors
    of M(1 :: L_out, 5, R) belong to exactly 6 shape families. -/
theorem macroStep_M_cons_1_5_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (1 :: L_out) 5 R)) :
    -- M_Config side
    (∃ d R', cfg = .M [] 7 (d :: R') ∧ L_out = [] ∧ R = (d + 1) :: R' ∧ k = 21)
    ∨ (∃ d R', cfg = .M (4 :: 1 :: L_out) 3 (d :: R')
        ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    -- M0_Config side
    ∨ (cfg = .M0 [2] [1] ∧ L_out = [] ∧ R = [1] ∧ k = 29)
    ∨ (cfg = .M0 (2 :: 1 :: L_out) [2] ∧ R = [1] ∧ k = 8)
    ∨ (∃ d R', cfg = .M0 (2 :: 1 :: L_out) (2 :: d :: R')
        ∧ R = (d + 1) :: R' ∧ k = 8)
    ∨ (cfg = .M0 (1 :: 1 :: L_out) [4] ∧ R = [1, 1] ∧ k = 19) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨c', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨a, hcfg, hk, htgt⟩
  | ⟨a, L', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨a, L', hcfg, hk, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 2 — M (a::L') 3 (d::R'), target M L' (a+1) (1::(d+1)::R') = M (1::L_out) 5 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha4 : a = 4 := by omega
    subst hL'; subst ha4
    right; left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · -- D3: sweep — needs invariant a ≥ 1 to discriminate (a+1=1 forces a=0)
    subst hcfg
    have ha : _ := (AllGe1_cons.mp hinv.1).1
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    omega
  · ms_inj_all  -- D4
  · -- D5: Producer 1 — M [] (c'+4) (d::R'), target M [1] (c'+2) ((d+1)::R') = M (1::L_out) 5 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨_, hL_out⟩, hc, hR_eq⟩ := htgt
    have hc3 : c' = 3 := by omega
    subst hc3
    left; exact ⟨d, R', hcfg, hL_out, hR_eq, hk⟩
  · -- D6: era_and_sweep — needs invariant b ≥ 1 to discriminate
    subst hcfg
    have hb : _ := (AllGe1_cons.mp (AllGe1_cons.mp hinv.1).2).1
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    omega
  · -- D7: Producer 3 — M0 [a+1] [1], target M [1] (a+4) [1] = M (1::L_out) 5 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨_, hL_out⟩, ha, hR_eq⟩ := htgt
    have ha1 : a = 1 := by omega
    subst ha1
    right; right; left; exact ⟨hcfg, hL_out, hR_eq, hk⟩
  · -- D8: Producer 4 — M0 (a::L') [2], target M L' (a+3) [1] = M (1::L_out) 5 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    right; right; right; left; exact ⟨hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D9
  · -- D10: Producer 6 — M0 (a::L') [4], target M L' (a+4) [1, 1] = M (1::L_out) 5 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha1 : a = 1 := by omega
    subst hL'; subst ha1
    right; right; right; right; right; exact ⟨hcfg, hR_eq, hk⟩
  · -- D11: zero_bounce — needs invariant a ≥ 1 to discriminate (a+4=1 impossible by Nat anyway)
    subst hcfg
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    omega
  · -- D12: Producer 5 — M0 (a::L') (2::d::R'), target M L' (a+3) ((d+1)::R') = M (1::L_out) 5 R
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    right; right; right; right; left; exact ⟨d, R', hcfg, hR_eq, hk⟩

-- ============================================================
-- Tier 3m: Layer 3 — backward analysis for Layer 2 predecessors
-- ============================================================
-- Layer 2 has 6 predecessor shapes. We need to exclude (or handle) each.
-- Starting with Shape 3: M0([2], [1]) — under MacroInvariant, has NO macroStep
-- predecessors at all (vacuous theorem).

/-- M0([2], [1]) is a macroStep dead-end: no cfg produces it via macroStep.
    Reasons:
    - sweep_to_zero variants: output R[0] = d+1 ≥ 1, but for R = [1], d = 0 violates invariant.
    - zero_bounce_to_zero: M0((a+4)::L', [1]). For L = [2]: a+4 = 2 impossible.
    - All other M0 dispatches produce M_Config or different R shapes. -/
theorem macroStep_no_M0_2_1_predecessor (cfg : MacroConfig) (k : Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 [2] [1])) : False := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, d, _, hcfg, _, htgt⟩
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
  · -- D1: cfg = M (a::L') 2 (d::R'); needs d ≥ 1 from invariant
    subst hcfg
    have hd : d ≥ 1 := (AllGe1_cons.mp hinv.2.2.1).1
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    omega
  ms_close

/-- Shape 4: M0(2 :: 1 :: L_out, [2]) has unique macroStep producer
    M(1 :: 1 :: L_out, 2, [1]) via sweep_to_zero. -/
theorem macroStep_M0_2_1_2_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 (2 :: 1 :: L_out) [2])) :
    cfg = .M (1 :: 1 :: L_out) 2 [1] ∧ k = 11 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, L', d, R', hcfg, hk, htgt⟩
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
  · -- D1 productive: target = M0 ((a+1)::L') ((d+1)::R') = M0 (2::1::L_out) [2]
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hd, hR'⟩ := htgt
    have ha1 : a = 1 := by omega
    have hd1 : d = 1 := by omega
    subst hL'; subst hR'; subst ha1; subst hd1
    exact ⟨hcfg, hk⟩
  all_goals simp_all [MacroConfig.M0.injEq, List.cons.injEq]

/-- Shape 5: M0(2 :: 1 :: L_out, 2 :: d :: R'') has unique macroStep producer
    M(1 :: 1 :: L_out, 2, 1 :: d :: R'') via sweep_to_zero. -/
theorem macroStep_M0_2_1_2_d_R_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (d : Nat) (R'' : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 (2 :: 1 :: L_out) (2 :: d :: R''))) :
    cfg = .M (1 :: 1 :: L_out) 2 (1 :: d :: R'') ∧ k = 11 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, L', d_p, R_p, hcfg, hk, htgt⟩
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
  · -- D1 productive: target = M0 ((a+1)::L') ((d_p+1)::R_p) = M0 (2::1::L_out) (2::d::R'')
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hd_p, hR_p⟩ := htgt
    have ha1 : a = 1 := by omega
    have hd_p1 : d_p = 1 := by omega
    subst hL'; subst hR_p; subst ha1; subst hd_p1
    exact ⟨hcfg, hk⟩
  all_goals simp_all [MacroConfig.M0.injEq, List.cons.injEq]

/-- M0(1 :: 1 :: L_out, [4]) is a macroStep dead-end under MacroInvariant.
    sweep_to_zero would require input L head a where a+1 = 1 (a=0), violating AllGe1. -/
theorem macroStep_no_M0_1_1_4_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 (1 :: 1 :: L_out) [4])) : False := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, _, _, _, hcfg, _, htgt⟩
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
  · -- D1: cfg = M (a::L') 2 (d::R'); needs a ≥ 1 from invariant
    subst hcfg
    have ha : a ≥ 1 := (AllGe1_cons.mp hinv.1).1
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    omega
  ms_close

-- ============================================================
-- Tier 4: R2 closure cascade — to be filled in
-- ============================================================
-- Top-level: OrbitReachable.not_R2.
-- Helper: not_M0_R_mid_has_1, not_M_R_mid_has_1.

-- TODO: (Tier 4 lemmas)

-- ============================================================
-- Layer 4: backward analysis for Layer 3 producers
-- ============================================================
-- Layer 3 introduced new producer shapes; Layer 4 characterizes their
-- predecessors. Shapes proven here:
-- 4a: M0([3], [4]) ← M([2], 2, [3])
-- 4b: M0([4], [2]) ← M([3], 2, [1])
-- 4c: M0([4], 2 :: d :: R') ← M([3], 2, [1, d, R'])
-- 4d: M(1 :: 1 :: L_out, 2, [1]) ← (Shape 4 producer)
-- 4e: M(1 :: 1 :: L_out, 2, [1, d, R'']) ← (Shape 5 producer)
-- 4f: M(3 :: 1 :: L_out, 5, _) ← (Shape 2 producer)
-- 4g: M([6], 3, _) ← (Shape 1 producer)
-- 4h: M(2 :: 4 :: 1 :: L_out, 3, _) ← reduces to Layer 1's L head = 2 at c=3

-- Layer 4 lemmas pattern: M0([a₀], [d₀]) (single-element L, single-element R)
-- with sweep_to_zero predecessor. The single producer is M([a₀-1], 2, [d₀-1]).

/-- Layer 4a: M0([3], [4]) has unique macroStep predecessor M([2], 2, [3]). -/
theorem macroStep_M0_3_4_predecessor (cfg : MacroConfig) (k : Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 [3] [4])) :
    cfg = .M [2] 2 [3] ∧ k = 11 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, L', d, R', hcfg, hk, htgt⟩
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
  · -- D1 (productive): target = .M0 ((a+1)::L') ((d+1)::R') = .M0 [3] [4]
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hd, hR'⟩ := htgt
    have ha2 : a = 2 := by omega
    have hd3 : d = 3 := by omega
    subst hL'; subst hR'; subst ha2; subst hd3
    exact ⟨hcfg, hk⟩
  all_goals simp_all [MacroConfig.M0.injEq, List.cons.injEq]

/-- Layer 4b: M0([4], [2]) has unique macroStep predecessor M([3], 2, [1]). -/
theorem macroStep_M0_4_2_predecessor (cfg : MacroConfig) (k : Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 [4] [2])) :
    cfg = .M [3] 2 [1] ∧ k = 11 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, L', d, R', hcfg, hk, htgt⟩
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
  · -- D1 productive: target = M0 ((a+1)::L') ((d+1)::R') = M0 [4] [2]
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hd, hR'⟩ := htgt
    have ha3 : a = 3 := by omega
    have hd1 : d = 1 := by omega
    subst hL'; subst hR'; subst ha3; subst hd1
    exact ⟨hcfg, hk⟩
  all_goals simp_all [MacroConfig.M0.injEq, List.cons.injEq]

/-- Layer 4d: M(1 :: 1 :: L_out, 2, [1]) is a macroStep dead-end.
    sweep at c=4 with output L head 1 requires input L head 0 (a+1=1), violating AllGe1.
    sweep_left_empty produces L = [1] (length 1), not 1 :: 1 :: L_out (length ≥ 2). -/
theorem macroStep_no_M_1_1_2_1_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (1 :: 1 :: L_out) 2 [1])) : False := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, _, htgt⟩
  | ⟨a, c', L', d, R', hcfg, _, htgt⟩
  | ⟨_, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, htgt⟩
  | ⟨_, _, _, htgt⟩
  | ⟨_, _, _, _, htgt⟩
  | ⟨_, _, _, _, htgt⟩
  | ⟨_, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, htgt⟩
  | ⟨_, _, _, _, _, _, htgt⟩
  -- D1, D2: M0 target / cons-list mismatch — simp_all closes
  · simp_all [MacroConfig.M0.injEq, List.cons.injEq]
  · simp_all [List.cons.injEq]
  -- D3: sweep, needs a ≥ 1 from invariant
  · subst hcfg
    have ha : a ≥ 1 := (AllGe1_cons.mp hinv.1).1
    simp only [MacroConfig.M.injEq, List.cons.injEq] at htgt
    omega
  ms_close

/-- Layer 4c: M0([4], 2 :: d :: R') has unique macroStep predecessor
    M([3], 2, [1, d, R']). -/
theorem macroStep_M0_4_2_d_R_predecessor (cfg : MacroConfig) (k : Nat)
    (d : Nat) (R'' : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 [4] (2 :: d :: R''))) :
    cfg = .M [3] 2 (1 :: d :: R'') ∧ k = 11 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, L', d_p, R_p, hcfg, hk, htgt⟩
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
  · -- D1 productive: target = M0 ((a+1)::L') ((d_p+1)::R_p) = M0 [4] (2::d::R'')
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hd_p, hR_p⟩ := htgt
    have ha3 : a = 3 := by omega
    have hd_p1 : d_p = 1 := by omega
    subst hL'; subst hR_p; subst ha3; subst hd_p1
    exact ⟨hcfg, hk⟩
  all_goals simp_all [MacroConfig.M0.injEq, List.cons.injEq]

/-- Layer 4e: M(1 :: 1 :: L_out, 2, 1 :: d :: R'') has unique macroStep predecessor
    M(1 :: 1 :: 1 :: L_out, 3, d_p :: R'') via sweep_and_shift, with d = d_p + 1.
    All other dispatches return none or invariant-violating shapes.
    NOTE: predecessor has L head = 1 at c=3, recursing into Layer 5+. -/
theorem macroStep_M_1_1_2_1_d_R_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (d : Nat) (R'' : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (1 :: 1 :: L_out) 2 (1 :: d :: R''))) :
    ∃ d_p, d = d_p + 1 ∧ cfg = .M (1 :: 1 :: 1 :: L_out) 3 (d_p :: R'') ∧ k = 19 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d_p, R_p, hcfg, hk, htgt⟩
  | ⟨_, _, _, _, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2 productive: cfg = M (a::L') 3 (d_p::R_p), target = M L' (a+1) (1::(d_p+1)::R_p)
    --                                            = M (1::1::L_out) 2 (1::d::R'')
    ms_inj at htgt
    obtain ⟨hL', ha, _, hd_eq, rfl⟩ := htgt
    have ha1 : a = 1 := by omega
    subst hL'; subst ha1
    exact ⟨d_p, hd_eq, hcfg, hk⟩
  ms_close

/-- Layer 4g: M([6], 3, R) has 3 macroStep predecessors:
    1. M([2, 6], 3, d :: R') via sweep_and_shift (recurses to Layer 1).
    2. M([5], 5, d :: R') via sweep at c=5.
    3. M0([2], [6]) via zero_bounce.
    Other M0 dispatches with cursor 3 require a = 0 (invariant violation). -/
theorem macroStep_M_6_3_predecessor (cfg : MacroConfig) (k : Nat)
    (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [6] 3 R)) :
    (∃ d R', cfg = .M [2, 6] 3 (d :: R') ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    ∨ (∃ d R', cfg = .M [5] 5 (d :: R') ∧ R = (d + 1) :: R' ∧ k = 17)
    ∨ (cfg = .M0 [2] [6] ∧ R = [1] ∧ k = 15) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨a, c', L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨a, z, L', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 1 — cfg = M (a::L') 3 (d::R'), target = M L' (a+1) (1::(d+1)::R') = M [6] 3 R
    ms_inj at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · -- D3: Producer 2 — cfg = M (a::L') (c'+4) (d::R'), target = M ((a+1)::L') (c'+2) ((d+1)::R')
    ms_inj at htgt
    obtain ⟨⟨ha, hL'⟩, hc, hR_eq⟩ := htgt
    have ha5 : a = 5 := by omega
    have hc1 : c' = 1 := by omega
    subst hL'; subst ha5; subst hc1
    right; left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D4
  · ms_inj_all  -- D5
  · -- D6: era_and_sweep, target M ((b+1)::L') (a+4) [1] = M [6] 3 R
    -- a+4 = 3 impossible by Nat
    subst hcfg; ms_inj at htgt; omega
  · ms_inj_all  -- D7
  · -- D8: zero_two_solo, target M L' (a+3) [1] = M [6] 3 R
    -- a+3 = 3 (a=0), needs invariant a ≥ 1
    subst hcfg
    have ha_inv := (AllGe1_cons.mp hinv.1).1
    ms_inj at htgt; omega
  · ms_inj_all  -- D9
  · -- D10: zero_bounce_and_shift, target M L' (a+4) [1, 1] = M [6] 3 R
    -- a+4 = 3 impossible
    subst hcfg; ms_inj at htgt; omega
  · -- D11: Producer 3 — cfg = M0 (a::L') [z+5], target M ((a+4)::L') (z+2) [1] = M [6] 3 R
    ms_inj at htgt
    obtain ⟨⟨ha, hL'⟩, hz, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    have hz1 : z = 1 := by omega
    subst hL'; subst ha2; subst hz1
    right; right; exact ⟨hcfg, hR_eq, hk⟩
  · -- D12: zero_two, target M L' (a+3) ((d+1)::R') = M [6] 3 R
    -- a+3 = 3 (a=0), needs invariant a ≥ 1
    subst hcfg
    have ha_inv := (AllGe1_cons.mp hinv.1).1
    ms_inj at htgt; omega

/-- Layer 4h: M(2 :: 4 :: 1 :: L_out, 3, R) — instance of Layer 1's `M (2::_) 3 _` lemma. -/
theorem macroStep_M_2_4_1_3_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (2 :: 4 :: 1 :: L_out) 3 R)) :
    (∃ d R', cfg = .M (2 :: 2 :: 4 :: 1 :: L_out) 3 (d :: R')
        ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    ∨ (∃ d R', cfg = .M (1 :: 4 :: 1 :: L_out) 5 (d :: R') ∧ R = (d + 1) :: R' ∧ k = 17) :=
  macroStep_M_cons_2_3_predecessor cfg k (4 :: 1 :: L_out) R hinv h

/-- Layer 4f: M(3 :: 1 :: L_out, 5, R) has 6 macroStep predecessors. -/
theorem macroStep_M_3_1_5_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (3 :: 1 :: L_out) 5 R)) :
    -- M_Config side
    (∃ d R', cfg = .M (4 :: 3 :: 1 :: L_out) 3 (d :: R')
        ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    ∨ (∃ d R', cfg = .M (2 :: 1 :: L_out) 7 (d :: R') ∧ R = (d + 1) :: R' ∧ k = 21)
    -- M0_Config side
    ∨ (cfg = .M0 (2 :: 2 :: 1 :: L_out) [1] ∧ R = [1] ∧ k = 29)
    ∨ (cfg = .M0 (2 :: 3 :: 1 :: L_out) [2] ∧ R = [1] ∧ k = 8)
    ∨ (cfg = .M0 (1 :: 3 :: 1 :: L_out) [4] ∧ R = [1, 1] ∧ k = 19)
    ∨ (∃ d R', cfg = .M0 (2 :: 3 :: 1 :: L_out) (2 :: d :: R')
        ∧ R = (d + 1) :: R' ∧ k = 8) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨a, c', L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨a, b, L', hcfg, hk, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨a, L', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨a, L', hcfg, hk, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 1 — cfg = M (a::L') 3 (d::R'), target = M L' (a+1) (1::(d+1)::R')
    ms_inj at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha4 : a = 4 := by omega
    subst hL'; subst ha4
    left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · -- D3: Producer 2 — cfg = M (a::L') (c'+4) (d::R'), target = M ((a+1)::L') (c'+2) ((d+1)::R')
    ms_inj at htgt
    obtain ⟨⟨ha, hL'⟩, hc, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    have hc3 : c' = 3 := by omega
    subst hL'; subst ha2; subst hc3
    right; left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D4
  · ms_inj_all  -- D5
  · -- D6: Producer 3 — cfg = M0 ((a+1)::b::L') [1], target = M ((b+1)::L') (a+4) [1]
    ms_inj at htgt
    obtain ⟨⟨hb, hL'⟩, ha_eq, hR_eq⟩ := htgt
    have ha1 : a = 1 := by omega
    have hb2 : b = 2 := by omega
    subst hL'; subst ha1; subst hb2
    right; right; left; exact ⟨hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D7
  · -- D8: Producer 4 — cfg = M0 (a::L') [2], target = M L' (a+3) [1]
    ms_inj at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    right; right; right; left; exact ⟨hcfg, hR_eq, hk⟩
  · ms_inj_all  -- D9
  · -- D10: Producer 5 — cfg = M0 (a::L') [4], target = M L' (a+4) [1, 1]
    ms_inj at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha1 : a = 1 := by omega
    subst hL'; subst ha1
    right; right; right; right; left; exact ⟨hcfg, hR_eq, hk⟩
  · -- D11: zero_bounce, target M ((a+4)::L') (z+2) [1] = M (3::1::L_out) 5 R
    -- (a+4)::L' = 3::1::L_out → a+4 = 3 impossible
    subst hcfg; ms_inj at htgt; omega
  · -- D12: Producer 6 — cfg = M0 (a::L') (2::d::R'), target = M L' (a+3) ((d+1)::R')
    ms_inj at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    right; right; right; right; right; exact ⟨d, R', hcfg, hR_eq, hk⟩

-- ============================================================
-- Layer 5: backward analysis for Layer 4 producers (Phase A — observation)
-- ============================================================
-- Goal: empirically test cascade termination conjecture. Add a representative
-- subset of Layer 5 lemmas to observe whether new shapes opened by Layer 4
-- close back to existing layers or open more.

/-- Layer 5: M(1 :: L_out, 3, R) — generalization handling 4e's continuation
    (M(1::1::1::L_out, 3, _)) and 4c's continuation (M([1, 3], 3, _)).
    2 producers:
    1. M(2 :: 1 :: L_out, 3, _) via sweep_and_shift — RECURSES TO LAYER 1.
    2. M([], 5, _) via sweep_left_empty (only when L_out = []) — NEW SHAPE. -/
theorem macroStep_M_cons_1_3_predecessor (cfg : MacroConfig) (k : Nat)
    (L_out : List Nat) (R : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M (1 :: L_out) 3 R)) :
    (∃ d R', cfg = .M (2 :: 1 :: L_out) 3 (d :: R') ∧ R = 1 :: (d + 1) :: R' ∧ k = 19)
    ∨ (L_out = [] ∧ ∃ d R', cfg = .M [] 5 (d :: R') ∧ R = (d + 1) :: R' ∧ k = 17) := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, _, _, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨c', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Producer 1 — cfg = M (a::L') 3 (d::R'), target = M L' (a+1) (1::(d+1)::R')
    ms_inj at htgt
    obtain ⟨hL', ha, hR_eq⟩ := htgt
    have ha2 : a = 2 := by omega
    subst hL'; subst ha2
    left; exact ⟨d, R', hcfg, hR_eq, hk⟩
  · -- D3: invariant violation (a + 1 = 1 needs a = 0)
    subst hcfg
    have ha := (AllGe1_cons.mp hinv.1).1
    ms_inj at htgt; omega
  · ms_inj_all  -- D4
  · -- D5: Producer 2 — cfg = M [] (c'+4) (d::R'), target M [1] (c'+2) ((d+1)::R')
    ms_inj at htgt
    obtain ⟨⟨_, hL_out⟩, hc, hR_eq⟩ := htgt
    have hc1 : c' = 1 := by omega
    subst hc1
    right; exact ⟨hL_out, d, R', hcfg, hR_eq, hk⟩
  ms_close

/-- Layer 5: M([2], 2, [3]) — Layer 4a's continuation. Unique predecessor:
    M([1], 4, [2]) via sweep at c=4 (NEW SHAPE for Layer 6). -/
theorem macroStep_M_2_2_3_predecessor (cfg : MacroConfig) (k : Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [2] 2 [3])) :
    cfg = .M [1] 4 [2] ∧ k = 15 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, _, _, htgt⟩
  | ⟨a, c', L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · ms_inj_all  -- D2
  · -- D3: Productive — cfg = M (a::L') (c'+4) (d::R'), target = M ((a+1)::L') (c'+2) ((d+1)::R')
    -- For = M [2] 2 [3]: a+1=2 (a=1), L'=[], c'+2=2 (c'=0), (d+1)::R' = [3] (d=2, R'=[]).
    ms_inj at htgt
    obtain ⟨⟨ha, hL'⟩, hc, hd, rfl⟩ := htgt
    have ha1 : a = 1 := by omega
    have hc0 : c' = 0 := by omega
    have hd2 : d = 2 := by omega
    subst hL'; subst ha1; subst hc0; subst hd2
    refine ⟨hcfg, ?_⟩; omega
  ms_close

/-- Layer 5: M([3], 2, [1]) — Layer 4b's continuation. DEAD-END under invariant
    (D3 sweep would need d_p = 0 in target's R, violating AllGe1 R). -/
theorem macroStep_no_M_3_2_1_predecessor (cfg : MacroConfig) (k : Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [3] 2 [1])) : False := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, _, _, htgt⟩
  | ⟨a, c', L', d, R', hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · ms_inj_all  -- D2
  · -- D3: cfg = M (a::L') (c'+4) (d::R'), target = M ((a+1)::L') (c'+2) ((d+1)::R')
    -- For = M [3] 2 [1]: a+1=3, c'+2=2, (d+1)::R' = [1] (d=0, R'=[]).
    -- d=0 violates invariant on cfg's R = (d::R') = [0].
    subst hcfg
    have hd_inv := (AllGe1_cons.mp hinv.2.2.1).1
    ms_inj at htgt; omega
  ms_close

/-- Layer 5: M([3], 2, 1::d::R'') — Layer 4c's continuation. Unique predecessor:
    M([1, 3], 3, d_p::R'') via sweep_and_shift, with d = d_p + 1.
    This is an instance of M(1::L_out, 3, _) (Layer 5 (1)) with L_out = [3]. -/
theorem macroStep_M_3_2_1_d_R_predecessor (cfg : MacroConfig) (k : Nat)
    (d : Nat) (R'' : List Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M [3] 2 (1 :: d :: R''))) :
    ∃ d_p, d = d_p + 1 ∧ cfg = .M [1, 3] 3 (d_p :: R'') ∧ k = 19 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨_, _, _, _, hcfg, _, htgt⟩
  | ⟨a, L', d_p, R_p, hcfg, hk, htgt⟩
  | ⟨a, c', L', d_p, R_p, hcfg, hk, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, hcfg, _, htgt⟩
  | ⟨_, _, _, hcfg, _, htgt⟩
  | ⟨_, _, _, _, hcfg, _, htgt⟩
  · ms_inj_all  -- D1
  · -- D2: Productive — cfg = M (a::L') 3 (d_p::R_p), target = M L' (a+1) (1::(d_p+1)::R_p)
    --                                              = M [3] 2 (1::d::R'')
    ms_inj at htgt
    obtain ⟨hL', ha, _, hd_eq, rfl⟩ := htgt
    have ha1 : a = 1 := by omega
    subst hL'; subst ha1
    exact ⟨d_p, hd_eq, hcfg, hk⟩
  · -- D3: cfg = M (a::L') (c'+4) (d_p::R_p), invariant violation (d_p = 0)
    subst hcfg
    have hd_inv := (AllGe1_cons.mp hinv.2.2.1).1
    ms_inj at htgt; omega
  ms_close

/-- Layer 5: M0([2], [6]) — Layer 4g's continuation (third producer).
    Unique predecessor: M([1], 2, [5]) via sweep_to_zero (NEW SHAPE for Layer 6). -/
theorem macroStep_M0_2_6_predecessor (cfg : MacroConfig) (k : Nat)
    (hinv : MacroInvariant cfg)
    (h : macroStep cfg = some (k, .M0 [2] [6])) :
    cfg = .M [1] 2 [5] ∧ k = 11 := by
  rcases macroStep_eq_some_cases cfg k _ h with
    ⟨a, L', d, R', hcfg, hk, htgt⟩
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
  · -- D1 productive: target = M0 ((a+1)::L') ((d+1)::R') = M0 [2] [6]
    simp only [MacroConfig.M0.injEq, List.cons.injEq] at htgt
    obtain ⟨⟨ha, hL'⟩, hd, hR'⟩ := htgt
    have ha1 : a = 1 := by omega
    have hd5 : d = 5 := by omega
    subst hL'; subst hR'; subst ha1; subst hd5
    exact ⟨hcfg, hk⟩
  all_goals simp_all [MacroConfig.M0.injEq, List.cons.injEq]

-- ============================================================
-- Tier 5: R3 narrowed closure cascade — to be filled in
-- ============================================================
-- Top-level: OrbitReachable.not_R3_narrow.
-- Reuses Tier 4's "no 1 in middle" invariant.

-- TODO: (Tier 5 lemmas)

-- ============================================================
-- Tier 6: wire-up — replace axiom invocations
-- ============================================================
-- Build a new `orbit_progress_direct` that dispatches axiom cases via
-- the not_R1/R2/R3 lemmas, replacing the axiom invocations entirely.

-- TODO: (Tier 6 wire-up)

end Sweeper
