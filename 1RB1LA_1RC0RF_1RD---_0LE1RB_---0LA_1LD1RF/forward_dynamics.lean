/-
Forward dynamics proofs for axioms R2 and R3-narrow.

These prove the same statements as the `reach_multi_bounce_last_2_mid_1` and
`reach_multi_bounce_last_2_long` axioms in `machine.lean`, by composing the
existing macro rules (`macro_multi_bounce_general` + `macro_shift`) into a
direct raw-TM step chain. R1 is not addressed here — its forward dynamics
halts at step 31, so closure must go through the `OrbitReachable` cascade
(see `phase2.lean`).
-/

import machine
import phi

namespace Sweeper

open BusyLean

-- ============================================================
-- R2: M0(a :: L', [r' + 3, 1, 2]) — 3-run with middle = 1
-- ============================================================
-- Closed-form bridge:
--   r' = 0:  39 raw steps → M(L', a+4, [1, 1, 1, 1])
--   r' ≥ 1:  r' + 33 raw steps → M((a+4) :: L', r'+1, [1, 1, 1])
-- Both reach a MacroInvariant-valid macro config, so MacroProg holds.

/-- R2 case `r' = 0`: `M0(a :: L', [3, 1, 2])` reaches `M(L', a+4, [1,1,1,1])`
    in 39 raw TM steps via `multi_bounce_general` (R_mid=[1], rₙ=0) + 3 shifts. -/
theorem bridge_R2_zero (a : Nat) (L' : List Nat) :
    run sweeper (M0_Config (a :: L') [3, 1, 2]) 39 =
    M_Config L' (a + 4) [1, 1, 1, 1] := by
  -- Step 1 (21 steps): multi_bounce_general gives M(1 :: 1 :: (a+4) :: L', 1, [1])
  have h1 : run sweeper (M0_Config (a :: L') [3, 1, 2]) 21 =
      M_Config (1 :: 1 :: (a + 4) :: L') 1 [1] := by
    have := macro_multi_bounce_general a 0 0 L' [1]
      (by intro x hx; simp at hx; omega)
    simpa using this
  -- Step 2 (6 steps): shift to M(1 :: (a+4) :: L', 1, [1, 1])
  have h2 : run sweeper (M_Config (1 :: 1 :: (a + 4) :: L') 1 [1]) 6 =
      M_Config (1 :: (a + 4) :: L') 1 [1, 1] := by
    have := macro_shift 0 1 (1 :: (a + 4) :: L') []
    simpa using this
  -- Step 3 (6 steps): shift to M((a+4) :: L', 1, [1, 1, 1])
  have h3 : run sweeper (M_Config (1 :: (a + 4) :: L') 1 [1, 1]) 6 =
      M_Config ((a + 4) :: L') 1 [1, 1, 1] := by
    have := macro_shift 0 1 ((a + 4) :: L') [1]
    simpa using this
  -- Step 4 (6 steps): shift to M(L', a+4, [1, 1, 1, 1])
  have h4 : run sweeper (M_Config ((a + 4) :: L') 1 [1, 1, 1]) 6 =
      M_Config L' (a + 4) [1, 1, 1, 1] := by
    have := macro_shift (a + 3) 1 L' [1, 1]
    simpa using this
  -- Chain
  rw [show (39 : Nat) = 21 + (6 + (6 + 6)) from rfl,
    run_add, h1, run_add, h2, run_add, h3, h4]

/-- Invariant preservation for R2 case `r' = 0`. -/
theorem invariant_R2_zero {a : Nat} {L' : List Nat}
    (h : MacroInvariant (.M0 (a :: L') [3, 1, 2])) :
    MacroInvariant (.M L' (a + 4) [1, 1, 1, 1]) := by
  have hL := h.1; rw [AllGe1_cons] at hL
  exact ⟨hL.2, by omega, ⟨by omega, by omega, by omega, by omega, trivial⟩,
         List.cons_ne_nil _ _⟩

/-- R2 case `r' ≥ 1` (parameterized as `r + 1`): `M0(a :: L', [r + 4, 1, 2])`
    reaches `M((a + 4) :: L', r + 2, [1, 1, 1])` in `r + 34` raw TM steps via
    `multi_bounce_general` (R_mid=[1], rₙ=0) + 2 shifts. -/
theorem bridge_R2_pos (a r : Nat) (L' : List Nat) :
    run sweeper (M0_Config (a :: L') [r + 4, 1, 2]) (r + 34) =
    M_Config ((a + 4) :: L') (r + 2) [1, 1, 1] := by
  -- Step 1 (r + 22 steps): multi_bounce_general (with multi_bounce param r := r+1)
  -- gives M(1 :: (r+2) :: (a+4) :: L', 1, [1])
  have h1 : run sweeper (M0_Config (a :: L') [r + 4, 1, 2]) (r + 22) =
      M_Config (1 :: (r + 2) :: (a + 4) :: L') 1 [1] := by
    have := macro_multi_bounce_general a (r + 1) 0 L' [1]
      (by intro x hx; simp at hx; omega)
    simpa [show r + 1 + 3 = r + 4 from by omega,
           show r + 1 + 0 + 3 * 1 + 1 + 17 = r + 22 from by omega,
           show r + 1 + 1 = r + 2 from by omega] using this
  -- Step 2 (6 steps): shift to M((r+2) :: (a+4) :: L', 1, [1, 1])
  have h2 : run sweeper (M_Config (1 :: (r + 2) :: (a + 4) :: L') 1 [1]) 6 =
      M_Config ((r + 2) :: (a + 4) :: L') 1 [1, 1] := by
    have := macro_shift 0 1 ((r + 2) :: (a + 4) :: L') []
    simpa using this
  -- Step 3 (6 steps): shift to M((a+4) :: L', r+2, [1, 1, 1])
  have h3 : run sweeper (M_Config ((r + 2) :: (a + 4) :: L') 1 [1, 1]) 6 =
      M_Config ((a + 4) :: L') (r + 2) [1, 1, 1] := by
    have := macro_shift (r + 1) 1 ((a + 4) :: L') [1]
    simpa [show r + 1 + 1 = r + 2 from by omega] using this
  -- Chain
  rw [show (r + 34 : Nat) = (r + 22) + (6 + 6) from by omega,
    run_add, h1, run_add, h2, h3]

/-- Invariant preservation for R2 case `r' ≥ 1`. -/
theorem invariant_R2_pos {a r : Nat} {L' : List Nat}
    (h : MacroInvariant (.M0 (a :: L') [r + 4, 1, 2])) :
    MacroInvariant (.M ((a + 4) :: L') (r + 2) [1, 1, 1]) := by
  have hL := h.1; rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, hL.2⟩, by omega,
         ⟨by omega, by omega, by omega, trivial⟩, List.cons_ne_nil _ _⟩

/-- R2 axiom replacement: `M0(a :: L', (r' + 3) :: ([1] ++ [2]))` continues
    in `k > 0` raw TM steps to a non-halted MacroProg config. Same statement
    as `axiom reach_multi_bounce_last_2_mid_1` in `machine.lean`. -/
theorem thm_reach_multi_bounce_last_2_mid_1 {a r' : Nat} {L' : List Nat}
    (hinv : MacroInvariant (.M0 (a :: L') ((r' + 3) :: ([1] ++ [2])))) :
    ∃ k, 0 < k ∧
      MacroProg (run sweeper (M0_Config (a :: L') ((r' + 3) :: ([1] ++ [2]))) k) ∧
      (run sweeper (M0_Config (a :: L') ((r' + 3) :: ([1] ++ [2]))) k).state ≠ none := by
  -- ([1] ++ [2]) reduces to [1, 2]; the input is M0(a :: L', [r'+3, 1, 2]).
  -- Case-split on r'.
  match r' with
  | 0 =>
    -- 39 steps to M(L', a + 4, [1, 1, 1, 1])
    refine ⟨39, by omega, ?_, ?_⟩
    · refine ⟨.M L' (a + 4) [1, 1, 1, 1], ?_, ?_⟩
      · show run sweeper (M0_Config (a :: L') ((0 + 3) :: ([1] ++ [2]))) 39 =
          (MacroConfig.M L' (a + 4) [1, 1, 1, 1]).toConfig
        rw [MacroConfig.toConfig_M]
        simpa using bridge_R2_zero a L'
      · exact invariant_R2_zero (by simpa using hinv)
    · show (run sweeper (M0_Config (a :: L') ((0 + 3) :: ([1] ++ [2]))) 39).state ≠ none
      have h := bridge_R2_zero a L'
      have heq : M0_Config (a :: L') ((0 + 3) :: ([1] ++ [2])) =
          M0_Config (a :: L') [3, 1, 2] := by simp
      rw [heq, h]; exact M_Config_state_ne_none _ _ _
  | r + 1 =>
    -- r + 34 steps to M((a + 4) :: L', r + 2, [1, 1, 1])
    have heq : ((r + 1 + 3) :: ([1] ++ [2]) : List Nat) = [r + 4, 1, 2] := by
      rw [show r + 1 + 3 = r + 4 from by omega]; rfl
    refine ⟨r + 34, by omega, ?_, ?_⟩
    · refine ⟨.M ((a + 4) :: L') (r + 2) [1, 1, 1], ?_, ?_⟩
      · rw [MacroConfig.toConfig_M, heq]; exact bridge_R2_pos a r L'
      · exact invariant_R2_pos (heq ▸ hinv)
    · rw [heq]; rw [bridge_R2_pos a r L']
      exact M_Config_state_ne_none _ _ _

-- ============================================================
-- R3-narrow: M0(a :: L', (r' + 3) :: e :: middle_init ++ [1, 2])
-- ============================================================
-- Forward dynamics for the "easy" half of R3-narrow: when the FIRST
-- post-leading element ≥ 2 (i.e., either `mi = []` with `e ≥ 2`, or
-- `mi = init ++ [last]` with `last ≥ 2`). Bridge:
--   r' + e + List.sum mi + 3 * mi.length + 36 raw steps.
-- The "hard" half (effective_first = 1, requires shifting through trailing
-- 1s) is empirically never reached and not closed here — see TACTIC_PLAN.md.

/-- R3-narrow easy case `mi = []` with `e ≥ 2` (parameterized as `e + 2`):
    `M0(a :: L', [r' + 3, e + 2, 1, 2])` reaches
    `M((r' + 1) :: (a + 4) :: L', e + 2, [1, 1, 1])` in `r' + e + 38` steps. -/
theorem bridge_R3_narrow_empty (a r' e : Nat) (L' : List Nat) :
    run sweeper (M0_Config (a :: L') [r' + 3, e + 2, 1, 2]) (r' + e + 38) =
    M_Config ((r' + 1) :: (a + 4) :: L') (e + 2) [1, 1, 1] := by
  -- Step 1 (r' + e + 26 steps): multi_bounce_general with R_mid = [e+2, 1], rₙ = 0
  have h1 : run sweeper (M0_Config (a :: L') [r' + 3, e + 2, 1, 2]) (r' + e + 26) =
      M_Config (1 :: (e + 2) :: (r' + 1) :: (a + 4) :: L') 1 [1] := by
    have := macro_multi_bounce_general a r' 0 L' [e + 2, 1]
      (by intro x hx; simp at hx; rcases hx with h | h <;> omega)
    simpa [show r' + 0 + 3 * 2 + (e + 2 + (1 + 0)) + 17 = r' + e + 26 from by omega] using this
  -- Step 2 (6 steps): shift to M((e+2) :: (r'+1) :: (a+4) :: L', 1, [1, 1])
  have h2 : run sweeper (M_Config (1 :: (e + 2) :: (r' + 1) :: (a + 4) :: L') 1 [1]) 6 =
      M_Config ((e + 2) :: (r' + 1) :: (a + 4) :: L') 1 [1, 1] := by
    have := macro_shift 0 1 ((e + 2) :: (r' + 1) :: (a + 4) :: L') []
    simpa using this
  -- Step 3 (6 steps): shift to M((r'+1) :: (a+4) :: L', e+2, [1, 1, 1])
  have h3 : run sweeper (M_Config ((e + 2) :: (r' + 1) :: (a + 4) :: L') 1 [1, 1]) 6 =
      M_Config ((r' + 1) :: (a + 4) :: L') (e + 2) [1, 1, 1] := by
    have := macro_shift (e + 1) 1 ((r' + 1) :: (a + 4) :: L') [1]
    simpa [show e + 1 + 1 = e + 2 from by omega] using this
  rw [show (r' + e + 38 : Nat) = (r' + e + 26) + (6 + 6) from by omega,
    run_add, h1, run_add, h2, h3]

/-- Invariant preservation for R3-narrow empty case. -/
theorem invariant_R3_narrow_empty {a r' e : Nat} {L' : List Nat}
    (h : MacroInvariant (.M0 (a :: L') [r' + 3, e + 2, 1, 2])) :
    MacroInvariant (.M ((r' + 1) :: (a + 4) :: L') (e + 2) [1, 1, 1]) := by
  have hL := h.1; rw [AllGe1_cons] at hL
  exact ⟨AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL.2⟩⟩, by omega,
         ⟨by omega, by omega, by omega, trivial⟩, List.cons_ne_nil _ _⟩

/-- R3-narrow easy case `mi = init ++ [last + 2]` with `init` all ≥ 1 and `last + 2 ≥ 2`:
    `M0(a :: L', (r' + 3) :: e :: (init ++ [last + 2]) ++ [1, 2])` reaches
    `M(init.reverse ++ e :: (r' + 1) :: (a + 4) :: L', last + 2, [1, 1, 1])`
    in `r' + e + List.sum init + last + 3 * init.length + 41` steps. -/
theorem bridge_R3_narrow_cons (a r' e last : Nat) (L' init : List Nat)
    (he : e ≥ 1) (h_init : ∀ x ∈ init, x ≥ 1) :
    run sweeper (M0_Config (a :: L')
        ((r' + 3) :: e :: (init ++ [last + 2]) ++ [1, 2]))
      (r' + e + List.sum init + last + 3 * init.length + 41) =
    M_Config (init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') (last + 2) [1, 1, 1] := by
  -- R_mid = e :: init ++ [last + 2, 1], rₙ = 0.
  -- After multi_bounce_general:
  --   Steps: r' + 0 + 3 * (init.length + 3) + (e + init.sum + last + 3) + 17
  --        = r' + e + init.sum + last + 3 * init.length + 29.
  --   Output: M(R_mid.reverse ++ (r'+1)::(a+4)::L', 1, [1])
  --   R_mid.reverse = 1 :: (last+2) :: init.reverse ++ [e]
  --   So output L = 1 :: (last+2) :: init.reverse ++ e :: (r'+1) :: (a+4) :: L'.
  have h_mid : ∀ x ∈ (e :: init ++ [last + 2, 1] : List Nat), x ≥ 1 := by
    intro x hx
    -- e :: init ++ [last+2, 1] parses as (e :: init) ++ [last+2, 1].
    -- Decompose membership by sequential append + cons unfolding.
    rcases List.mem_append.mp hx with hx | hx
    · -- x ∈ e :: init
      rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact h_init x hx
    · -- x ∈ [last+2, 1]
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · rcases List.mem_singleton.mp hx with rfl
        omega
  have h1 : run sweeper (M0_Config (a :: L')
        ((r' + 3) :: e :: (init ++ [last + 2]) ++ [1, 2]))
      (r' + e + List.sum init + last + 3 * init.length + 29) =
      M_Config (1 :: (last + 2) :: init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') 1 [1] := by
    have := macro_multi_bounce_general a r' 0 L' (e :: init ++ [last + 2, 1]) h_mid
    -- this : run sweeper (M0_Config (a :: L') ((r' + 3) :: (e :: init ++ [last + 2, 1]) ++ [0 + 2]))
    --   (r' + 0 + 3 * (e :: init ++ [last + 2, 1]).length +
    --     List.sum (e :: init ++ [last + 2, 1]) + 17) =
    --   M_Config ((e :: init ++ [last + 2, 1]).reverse ++ (r' + 1) :: (a + 4) :: L') (0 + 1) [1]
    -- Need to show: input shape, step count, output shape match.
    have h_input : ((r' + 3) :: e :: (init ++ [last + 2]) ++ [1, 2] : List Nat) =
        ((r' + 3) :: (e :: init ++ [last + 2, 1]) ++ [0 + 2] : List Nat) := by
      simp [List.cons_append, List.append_assoc]
    have h_steps : r' + 0 + 3 * (e :: init ++ [last + 2, 1] : List Nat).length +
        List.sum (e :: init ++ [last + 2, 1] : List Nat) + 17 =
        r' + e + List.sum init + last + 3 * init.length + 29 := by
      simp [List.length_append, List.length_cons, List.sum_append, List.sum_cons,
            List.length_singleton, List.sum_singleton]; ring
    have h_outL : ((e :: init ++ [last + 2, 1] : List Nat).reverse ++
        (r' + 1) :: (a + 4) :: L' : List Nat) =
        1 :: (last + 2) :: init.reverse ++ e :: (r' + 1) :: (a + 4) :: L' := by
      simp [List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.cons_append, List.append_assoc, List.singleton_append]
    rw [h_input, h_steps.symm, h_outL.symm]
    -- Now need (0 + 1) = 1 for the cursor, simp handles it
    simpa using this
  -- Step 2 (6 steps): shift the leading 1
  have h2 : run sweeper (M_Config
      (1 :: (last + 2) :: init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') 1 [1]) 6 =
      M_Config ((last + 2) :: init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') 1 [1, 1] := by
    have := macro_shift 0 1
      ((last + 2) :: init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') []
    simpa using this
  -- Step 3 (6 steps): shift the (last + 2) head
  have h3 : run sweeper (M_Config
      ((last + 2) :: init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') 1 [1, 1]) 6 =
      M_Config (init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') (last + 2) [1, 1, 1] := by
    have := macro_shift (last + 1) 1
      (init.reverse ++ e :: (r' + 1) :: (a + 4) :: L') [1]
    simpa [show last + 1 + 1 = last + 2 from by omega] using this
  rw [show (r' + e + List.sum init + last + 3 * init.length + 41 : Nat) =
    (r' + e + List.sum init + last + 3 * init.length + 29) + (6 + 6) from by omega,
    run_add, h1, run_add, h2, h3]

/-- Invariant preservation for R3-narrow cons case. -/
theorem invariant_R3_narrow_cons {a r' e last : Nat} {L' init : List Nat}
    (h : MacroInvariant (.M0 (a :: L')
      ((r' + 3) :: e :: (init ++ [last + 2]) ++ [1, 2]))) :
    MacroInvariant (.M (init.reverse ++ e :: (r' + 1) :: (a + 4) :: L')
      (last + 2) [1, 1, 1]) := by
  have hL := h.1
  rw [AllGe1_cons] at hL
  have hR := h.2.1
  -- Decompose hR layer by layer to extract he and AllGe1 init.
  have hR1 : AllGe1 ((r' + 3) :: e :: (init ++ [last + 2]) : List Nat) :=
    AllGe1_of_append_left hR
  have ⟨_, hR2⟩ := AllGe1_cons.mp hR1
  have ⟨he, hR3⟩ := AllGe1_cons.mp hR2
  have h_init_All : AllGe1 init := AllGe1_of_append_left hR3
  refine ⟨?_, by omega, ⟨by omega, by omega, by omega, trivial⟩, List.cons_ne_nil _ _⟩
  -- AllGe1 (init.reverse ++ e :: (r'+1) :: (a+4) :: L')
  exact AllGe1_append (AllGe1_reverse h_init_All)
    (AllGe1_cons.mpr ⟨he, AllGe1_cons.mpr ⟨by omega,
      AllGe1_cons.mpr ⟨by omega, hL.2⟩⟩⟩)

-- ============================================================
-- General helper: shift through cursor-1 configs to MacroProg
-- ============================================================
-- Used to close the recursive ("hard") cases of R3-narrow where the L
-- list after multi_bounce has a prefix of 1s (from `mi.last = 1`, `e = 1`,
-- or `r' = 0`). The induction strips one L element per shift, prepending
-- a 1 to R, until the cursor lands on a non-1 element ≥ 2.
--
-- Termination: the L_full list has at least one element ≥ 2 (typically
-- `(a + 4) ≥ 5` from the input invariant). Each recursive call shrinks L.

/-- From `M_Config L 1 R` with cursor 1, R nonempty, AllGe1 lists, and at
    least one L element ≥ 2, the raw TM eventually reaches a MacroProg
    config (cursor ≥ 2). -/
theorem shift_to_macro_prog (L : List Nat) (R : List Nat)
    (h_R_ne : R ≠ []) (h_R_ge1 : AllGe1 R) (h_L_ge1 : AllGe1 L)
    (h_nonone : ∃ x ∈ L, x ≥ 2) :
    ∃ k, 0 < k ∧
      MacroProg (run sweeper (M_Config L 1 R) k) ∧
      (run sweeper (M_Config L 1 R) k).state ≠ none := by
  induction L generalizing R with
  | nil =>
    exfalso
    obtain ⟨x, hx, _⟩ := h_nonone
    exact List.not_mem_nil hx
  | cons a L_tail ih =>
    have ha : a ≥ 1 := (AllGe1_cons.mp h_L_ge1).1
    obtain ⟨d, R_tail, rfl⟩ := List.exists_cons_of_ne_nil h_R_ne
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have h_L_tail_ge1 : AllGe1 L_tail := (AllGe1_cons.mp h_L_ge1).2
    by_cases h_a'_zero : a' = 0
    · -- Head is 1 (a' = 0). Apply shift, recurse on L_tail.
      subst h_a'_zero
      have h_R_new_ge1 : AllGe1 (1 :: d :: R_tail) :=
        AllGe1_cons.mpr ⟨by omega, h_R_ge1⟩
      have h_R_new_ne : (1 :: d :: R_tail : List Nat) ≠ [] := List.cons_ne_nil _ _
      have h_tail_nonone : ∃ x ∈ L_tail, x ≥ 2 := by
        obtain ⟨x, hx, hx_ge2⟩ := h_nonone
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact ⟨x, hx, hx_ge2⟩
      obtain ⟨k_rest, hk_rest, hprog, hne⟩ :=
        ih (1 :: d :: R_tail) h_R_new_ne h_R_new_ge1 h_L_tail_ge1 h_tail_nonone
      refine ⟨6 + k_rest, by omega, ?_, ?_⟩
      · rw [run_add, macro_shift 0 d L_tail R_tail]
        exact hprog
      · rw [run_add, macro_shift 0 d L_tail R_tail]
        exact hne
    · -- Head is ≥ 2 (a' ≥ 1). One shift gives cursor ≥ 2, MacroProg.
      have ha' : a' ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_a'_zero
      refine ⟨6, by omega, ?_, ?_⟩
      · rw [macro_shift a' d L_tail R_tail]
        refine ⟨.M L_tail (a' + 1) (1 :: d :: R_tail), ?_, ?_⟩
        · rw [MacroConfig.toConfig_M]
        · refine ⟨h_L_tail_ge1, by omega, ?_, List.cons_ne_nil _ _⟩
          exact AllGe1_cons.mpr ⟨by omega, h_R_ge1⟩
      · rw [macro_shift a' d L_tail R_tail]
        exact M_Config_state_ne_none _ _ _

-- ============================================================
-- Full R3-narrow existence theorem (replaces axiom)
-- ============================================================

/-- R3-narrow axiom replacement: `M0(a :: L', (r' + 3) :: e :: middle_init ++ [1, 2])`
    continues. Uses `multi_bounce_general` + `shift_to_macro_prog` (which
    handles arbitrary leading-1 prefixes in the post-multi-bounce L). -/
theorem thm_reach_multi_bounce_last_2_long {a r' e : Nat} {L' middle_init : List Nat}
    (hinv : MacroInvariant
      (.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2]))) :
    ∃ k, 0 < k ∧
      MacroProg (run sweeper
        (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k) ∧
      (run sweeper (M0_Config (a :: L')
        ((r' + 3) :: e :: middle_init ++ [1, 2])) k).state ≠ none := by
  -- Extract invariant facts.
  have hL := hinv.1
  have hR := hinv.2.1
  have ha : a ≥ 1 := (AllGe1_cons.mp hL).1
  have hL' : AllGe1 L' := (AllGe1_cons.mp hL).2
  have hR1 : AllGe1 ((r' + 3) :: e :: middle_init : List Nat) :=
    AllGe1_of_append_left hR
  have ⟨_, hR2⟩ := AllGe1_cons.mp hR1
  have ⟨he, h_mi_All⟩ := AllGe1_cons.mp hR2
  -- Hypothesis for multi_bounce_general's R_mid = (e :: middle_init) ++ [1].
  have h_mid : ∀ x ∈ ((e :: middle_init) ++ [1] : List Nat), x ≥ 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact AllGe1_mem h_mi_All hx
    · rcases List.mem_singleton.mp hx with rfl
      omega
  -- Step 1: invoke multi_bounce_general and rewrite its input/output to clean form.
  have h_in_eq : ((r' + 3) :: e :: middle_init ++ [1, 2] : List Nat) =
      (r' + 3) :: ((e :: middle_init) ++ [1]) ++ [0 + 2] := by
    simp [List.cons_append, List.append_assoc]
  have h_mb_raw := macro_multi_bounce_general a r' 0 L' ((e :: middle_init) ++ [1]) h_mid
  -- Massage h_mb_raw into a clean bridge from the goal's input form.
  rw [← h_in_eq] at h_mb_raw
  -- Now h_mb_raw : run (M0_Config _ ((r' + 3) :: e :: middle_init ++ [1, 2])) k_mb_raw =
  --   M_Config L_after (0 + 1) [1]
  -- where L_after = ((e :: middle_init) ++ [1]).reverse ++ (r' + 1) :: (a + 4) :: L'.
  set L_after : List Nat :=
    ((e :: middle_init) ++ [1]).reverse ++ (r' + 1) :: (a + 4) :: L' with hL_after_def
  -- AllGe1 L_after
  have h_L_after_ge1 : AllGe1 L_after := by
    apply AllGe1_append
    · apply AllGe1_reverse
      apply AllGe1_append
      · exact AllGe1_cons.mpr ⟨he, h_mi_All⟩
      · exact AllGe1_singleton (by omega)
    · exact AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL'⟩⟩
  -- ∃ x ∈ L_after, x ≥ 2 (witness: a + 4 ≥ 5)
  have h_L_after_nonone : ∃ x ∈ L_after, x ≥ 2 := by
    refine ⟨a + 4, ?_, by omega⟩
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right
    exact List.mem_cons_self
  -- Step 2: apply shift_to_macro_prog
  obtain ⟨k_shift, hk_shift, hprog_shift, hne_shift⟩ :=
    shift_to_macro_prog L_after [1]
      (List.cons_ne_nil _ _)
      (AllGe1_singleton (by omega))
      h_L_after_ge1 h_L_after_nonone
  -- Step 3: combine. Extract k_mb from h_mb_raw.
  obtain ⟨k_mb, h_mb⟩ : ∃ k_mb, run sweeper
      (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k_mb =
        M_Config L_after (0 + 1) [1] :=
    ⟨_, h_mb_raw⟩
  refine ⟨k_mb + k_shift, by omega, ?_, ?_⟩
  · rw [run_add, h_mb]; exact hprog_shift
  · rw [run_add, h_mb]; exact hne_shift

-- ============================================================
-- Structural analysis of shift_to_macro_prog
-- ============================================================

/-- **Strong shift lemma**: `shift_to_macro_prog`'s witness has explicit
    structure — it splits `L` into a prefix `L_pre` of all 1s, a first
    ≥ 2 element `v`, and a suffix `L_suf`. The raw-TM run reaches
    `M_Config L_suf v R_out` for some `R_out`. The output also has the
    same Φ as the input (each shift preserves Φ; ΔΦ = 0). -/
theorem shift_to_macro_prog_strong (L R : List Nat)
    (h_R_ne : R ≠ []) (h_R_ge1 : AllGe1 R) (h_L_ge1 : AllGe1 L)
    (h_nonone : ∃ x ∈ L, x ≥ 2) :
    ∃ (k : Nat) (L_pre : List Nat) (v : Nat) (L_suf : List Nat) (R_out : List Nat),
      0 < k ∧
      L = L_pre ++ v :: L_suf ∧ (∀ x ∈ L_pre, x = 1) ∧ v ≥ 2 ∧
      run sweeper (M_Config L 1 R) k = M_Config L_suf v R_out ∧
      MacroInvariant (.M L_suf v R_out) ∧
      (MacroConfig.M L_suf v R_out).phi = (MacroConfig.M L 1 R).phi := by
  induction L generalizing R with
  | nil =>
    exfalso
    obtain ⟨x, hx, _⟩ := h_nonone
    exact List.not_mem_nil hx
  | cons a L_tail ih =>
    have ha : a ≥ 1 := (AllGe1_cons.mp h_L_ge1).1
    obtain ⟨d, R_tail, rfl⟩ := List.exists_cons_of_ne_nil h_R_ne
    have h_L_tail_ge1 : AllGe1 L_tail := (AllGe1_cons.mp h_L_ge1).2
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    by_cases h_a' : a' = 0
    · subst h_a'
      have h_R_new_ge1 : AllGe1 (1 :: d :: R_tail) :=
        AllGe1_cons.mpr ⟨by omega, h_R_ge1⟩
      have h_R_new_ne : (1 :: d :: R_tail : List Nat) ≠ [] := List.cons_ne_nil _ _
      have h_tail_nonone : ∃ x ∈ L_tail, x ≥ 2 := by
        obtain ⟨x, hx, hx_ge2⟩ := h_nonone
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact ⟨x, hx, hx_ge2⟩
      obtain ⟨k_rest, L_pre_rest, v, L_suf, R_out, hk_rest, h_split, h_pre_one,
              hv, hrun_rest, hinv', hphi⟩ :=
        ih (1 :: d :: R_tail) h_R_new_ne h_R_new_ge1 h_L_tail_ge1 h_tail_nonone
      refine ⟨6 + k_rest, 1 :: L_pre_rest, v, L_suf, R_out, by omega, ?_, ?_,
              hv, ?_, hinv', ?_⟩
      · simp [h_split, List.cons_append]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact h_pre_one x hx
      · rw [run_add, macro_shift 0 d L_tail R_tail, hrun_rest]
      · -- Φ-preservation: hphi gives output = (M L_tail 1 (1::d::R_tail)).phi.
        -- We want output = (M (1::L_tail) 1 (d::R_tail)).phi. Equal by simp.
        rw [hphi]
        simp only [MacroConfig.phi_M, List.sum_cons]
        omega
    · have ha' : a' ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_a'
      refine ⟨6, [], a' + 1, L_tail, 1 :: d :: R_tail, by omega, rfl, ?_,
              by omega, macro_shift a' d L_tail R_tail, ?_, ?_⟩
      · intro x hx; exact (List.not_mem_nil hx).elim
      · refine ⟨h_L_tail_ge1, by omega, AllGe1_cons.mpr ⟨by omega, h_R_ge1⟩,
                List.cons_ne_nil _ _⟩
      · -- One-shift Φ-preservation: M((a'+1)::L_tail, 1, d::R_tail) → M(L_tail, a'+1, 1::d::R_tail).
        simp only [MacroConfig.phi_M, List.sum_cons]
        omega

/-- Corollary: if `L` contains an element `x ≥ 5`, the shift output is
    never `M([], 3, R)` for any R. (For `x = v` we have c = v ≥ 5; for
    `x ∈ L_suf` we have L ≠ [].) Also exposes Φ-preservation: cfg's Φ
    equals the input M(L, 1, R)'s Φ.

    Strengthened (2026-05-07) to also expose the structural fact
    `v ≥ 5 ∨ ∃ x ∈ L_suf, x ≥ 5`: cfg' is M-shape and either its
    cursor or L_suf has a ≥5 element. Used to exclude cascade
    shapes (e.g. `mk_M_2spine_3` requires v=3 but also L_suf 2-spine,
    which contradicts the ∃ x ∈ L_suf, x ≥ 5 in the v < 5 case). -/
theorem shift_to_macro_prog_excludes_R1 (L R : List Nat)
    (h_R_ne : R ≠ []) (h_R_ge1 : AllGe1 R) (h_L_ge1 : AllGe1 L)
    (h_nonone : ∃ x ∈ L, x ≥ 2)
    (h_has_5 : ∃ x ∈ L, x ≥ 5) :
    ∃ (k : Nat) (cfg' : MacroConfig),
      0 < k ∧
      run sweeper (M_Config L 1 R) k = cfg'.toConfig ∧
      MacroInvariant cfg' ∧
      (∀ R', cfg' ≠ .M [] 3 R') ∧
      (∃ L_suf v R_out, cfg' = .M L_suf v R_out ∧
          (v ≥ 5 ∨ ∃ x ∈ L_suf, x ≥ 5)) ∧
      cfg'.phi = (MacroConfig.M L 1 R).phi := by
  obtain ⟨k, L_pre, v, L_suf, R_out, hk, h_split, h_pre_one, hv, hrun, hinv', hphi⟩ :=
    shift_to_macro_prog_strong L R h_R_ne h_R_ge1 h_L_ge1 h_nonone
  refine ⟨k, .M L_suf v R_out, hk, ?_, hinv', ?_, ?_, hphi⟩
  · rw [hrun, MacroConfig.toConfig_M]
  · intro R' hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hLsuf, hv_eq, _⟩ := hcfg
    obtain ⟨x, hx, hx_ge5⟩ := h_has_5
    rw [h_split] at hx
    rcases List.mem_append.mp hx with hx_pre | hx_post
    · have hx_eq_1 := h_pre_one x hx_pre
      omega
    · rcases List.mem_cons.mp hx_post with rfl | hx_suf
      · omega
      · rw [hLsuf] at hx_suf
        exact List.not_mem_nil hx_suf
  · -- strict_safe: ∃ L_suf v R_out, cfg' = M L_suf v R_out ∧ (v ≥ 5 ∨ ∃ x ∈ L_suf, x ≥ 5)
    refine ⟨L_suf, v, R_out, rfl, ?_⟩
    obtain ⟨x, hx, hx_ge5⟩ := h_has_5
    rw [h_split] at hx
    rcases List.mem_append.mp hx with hx_pre | hx_post
    · have hx_eq_1 := h_pre_one x hx_pre; omega
    · rcases List.mem_cons.mp hx_post with rfl | hx_suf
      · left; omega
      · right; exact ⟨x, hx_suf, hx_ge5⟩

/-- **Safe R3 closure**: like `thm_reach_multi_bounce_last_2_long` but
    additionally returns the structural exclusion `cfg' ≠ M([], 3, R)`
    via `shift_to_macro_prog_excludes_R1`, and exposes the Φ jump
    `cfg'.phi = predecessor.phi + 2` from composing
    `phi_macro_multi_bounce_general` (Δ=+2) with shift Δ=0. The
    `L_after` list always contains `a + 4 ≥ 5` (since `a ≥ 1` from
    `MacroInvariant`), so the safety property holds. Used in
    `orbit_progress`'s R3 case to discharge `step_R3`'s safety
    precondition. -/
theorem thm_reach_multi_bounce_last_2_long_safe
    {a r' e : Nat} {L' middle_init : List Nat}
    (hinv : MacroInvariant
      (.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2]))) :
    ∃ (k : Nat) (cfg' : MacroConfig), 0 < k ∧
      run sweeper
        (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k =
        cfg'.toConfig ∧
      MacroInvariant cfg' ∧
      (∀ R, cfg' ≠ .M [] 3 R) ∧
      -- Strict safe (2026-05-07): cfg' = M L_suf v R_out, and either there's
      -- a ≥5 element in L_suf, or v = a+4 with L_suf = L'. The first case
      -- excludes cascade shapes where L_suf is bounded; the second case
      -- exposes the predecessor structure for M0 backward chase.
      (∃ L_suf v R_out, cfg' = .M L_suf v R_out ∧
          ((∃ x ∈ L_suf, x ≥ 5) ∨ (v = a + 4 ∧ L_suf = L'))) ∧
      cfg'.phi =
        (MacroConfig.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])).phi + 2 := by
  -- Same setup as thm_reach_multi_bounce_last_2_long.
  have hL := hinv.1
  have hR := hinv.2.1
  have ha : a ≥ 1 := (AllGe1_cons.mp hL).1
  have hL' : AllGe1 L' := (AllGe1_cons.mp hL).2
  have hR1 : AllGe1 ((r' + 3) :: e :: middle_init : List Nat) :=
    AllGe1_of_append_left hR
  have ⟨_, hR2⟩ := AllGe1_cons.mp hR1
  have ⟨he, h_mi_All⟩ := AllGe1_cons.mp hR2
  have h_mid : ∀ x ∈ ((e :: middle_init) ++ [1] : List Nat), x ≥ 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact AllGe1_mem h_mi_All hx
    · rcases List.mem_singleton.mp hx with rfl
      omega
  -- Step 1: invoke macro_multi_bounce_general.
  have h_in_eq : ((r' + 3) :: e :: middle_init ++ [1, 2] : List Nat) =
      (r' + 3) :: ((e :: middle_init) ++ [1]) ++ [0 + 2] := by
    simp [List.cons_append, List.append_assoc]
  have h_mb_raw := macro_multi_bounce_general a r' 0 L' ((e :: middle_init) ++ [1]) h_mid
  rw [← h_in_eq] at h_mb_raw
  set L_after : List Nat :=
    ((e :: middle_init) ++ [1]).reverse ++ (r' + 1) :: (a + 4) :: L' with hL_after_def
  have h_L_after_ge1 : AllGe1 L_after := by
    apply AllGe1_append
    · apply AllGe1_reverse
      apply AllGe1_append
      · exact AllGe1_cons.mpr ⟨he, h_mi_All⟩
      · exact AllGe1_singleton (by omega)
    · exact AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL'⟩⟩
  have h_L_after_nonone : ∃ x ∈ L_after, x ≥ 2 := by
    refine ⟨a + 4, ?_, by omega⟩
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right
    exact List.mem_cons_self
  have h_L_after_has_5 : ∃ x ∈ L_after, x ≥ 5 := by
    refine ⟨a + 4, ?_, by omega⟩
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right
    exact List.mem_cons_self
  -- Step 2: apply shift_to_macro_prog_strong directly to get structural info.
  obtain ⟨k_shift, L_pre, v_out, L_suf, R_out, hk_shift, h_split, h_pre_one, hv_ge2,
          hrun_shift, hinv'_shift, hphi_shift⟩ :=
    shift_to_macro_prog_strong L_after [1]
      (List.cons_ne_nil _ _)
      (AllGe1_singleton (by omega))
      h_L_after_ge1 h_L_after_nonone
  -- Derive h_safe from the ≥5 element fact.
  have h_safe : ∀ R', (MacroConfig.M L_suf v_out R_out) ≠ .M [] 3 R' := by
    intro R' hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hLsuf, hv_eq, _⟩ := hcfg
    obtain ⟨x, hx, hx_ge5⟩ := h_L_after_has_5
    rw [h_split] at hx
    rcases List.mem_append.mp hx with hx_pre | hx_post
    · have := h_pre_one x hx_pre; omega
    · rcases List.mem_cons.mp hx_post with rfl | hx_suf
      · omega
      · rw [hLsuf] at hx_suf; exact List.not_mem_nil hx_suf
  -- Derive the NEW strict_safe: (∃ x ∈ L_suf, x ≥ 5) ∨ (v = a+4 ∧ L_suf = L')
  have h_strict_safe : ∃ L_suf' v R_out',
      (MacroConfig.M L_suf v_out R_out) = .M L_suf' v R_out' ∧
      ((∃ x ∈ L_suf', x ≥ 5) ∨ (v = a + 4 ∧ L_suf' = L')) := by
    refine ⟨L_suf, v_out, R_out, rfl, ?_⟩
    -- Case split: is (a+4) at v_out position (v_out = a+4) or in L_suf?
    -- L_after = [1] ++ middle_init.reverse ++ [e] ++ (r'+1) :: (a+4) :: L'.
    -- L_after = L_pre ++ v_out :: L_suf with L_pre all 1s.
    -- (a+4) is in L_after; since L_pre all 1s and a+4 ≥ 5 ≠ 1, (a+4) ∉ L_pre.
    -- So (a+4) = v_out OR (a+4) ∈ L_suf.
    -- Define the structural prefix.
    set prefix_L : List Nat :=
      ((e :: middle_init) ++ [1]).reverse ++ [r' + 1] with hprefix_def
    have h_after_eq : L_after = prefix_L ++ (a + 4) :: L' := by
      rw [hL_after_def]
      simp [hprefix_def, List.append_assoc]
    -- We have: L_pre ++ v_out :: L_suf = prefix_L ++ (a + 4) :: L'
    have h_eq : L_pre ++ v_out :: L_suf = prefix_L ++ (a + 4) :: L' := by
      rw [← h_after_eq]; exact h_split.symm
    -- Apply List.append_eq_append_iff to do case analysis.
    rcases List.append_eq_append_iff.mp h_eq with
      ⟨k, hLpre_eq, h_tail⟩ | ⟨k, hpre_eq, h_tail⟩
    · -- prefix_L = L_pre ++ k AND v_out :: L_suf = k ++ (a + 4) :: L'
      cases k with
      | nil =>
        -- prefix_L = L_pre, v_out :: L_suf = (a + 4) :: L'.
        right
        injection h_tail with hv_eq hL_suf_eq
        exact ⟨hv_eq, hL_suf_eq⟩
      | cons k_head k_tail =>
        -- v_out :: L_suf = (k_head :: k_tail) ++ (a + 4) :: L'
        -- Cons-injection: v_out = k_head, L_suf = k_tail ++ (a + 4) :: L'.
        injection h_tail with _hv_eq hL_suf_eq
        -- L_suf has (a + 4) somewhere (in the trailing part).
        left
        refine ⟨a + 4, ?_, by omega⟩
        rw [hL_suf_eq]
        apply List.mem_append_right
        exact List.mem_cons_self
    · -- L_pre = prefix_L ++ k AND (a + 4) :: L' = k ++ v_out :: L_suf
      cases k with
      | nil =>
        -- L_pre = prefix_L, (a + 4) :: L' = v_out :: L_suf.
        right
        injection h_tail with hv_eq hL_suf_eq
        exact ⟨hv_eq.symm, hL_suf_eq.symm⟩
      | cons k_head k_tail =>
        -- (a + 4) :: L' = (k_head :: k_tail) ++ v_out :: L_suf
        -- Cons-injection: a + 4 = k_head; k_head ∈ L_pre → all 1 → contradiction.
        injection h_tail with hkh _
        have h_kh_in : k_head ∈ L_pre := by
          rw [hpre_eq]; exact List.mem_append_right _ List.mem_cons_self
        have := h_pre_one k_head h_kh_in
        omega
  -- Step 3: combine.
  obtain ⟨k_mb, h_mb⟩ : ∃ k_mb, run sweeper
      (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k_mb =
        M_Config L_after (0 + 1) [1] :=
    ⟨_, h_mb_raw⟩
  refine ⟨k_mb + k_shift, .M L_suf v_out R_out, by omega, ?_, hinv'_shift,
          h_safe, h_strict_safe, ?_⟩
  · rw [run_add, h_mb, hrun_shift, MacroConfig.toConfig_M]
  · -- phi computation
    rw [hphi_shift]
    simp only [hL_after_def, MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_append, List.sum_cons, List.sum_nil,
               List.sum_reverse]
    omega

-- ============================================================
-- Inverse-shift case decomposition
-- ============================================================

/-- **Inverse-shift 4-case decomposition**: given the structural list equation
    `1 :: middle_init.reverse ++ e :: (r'+1) :: (a+4) :: L' = L_pre ++ v :: L_suf`
    with `L_pre` all 1s, `v ≥ 2`, and `AllGe1` invariants, exactly one of the
    following 4 structural cases holds. Used to invert
    `shift_to_macro_prog_strong` applied to the multi-bounce output. -/
theorem shift_inverse_4cases
    (a r' e : Nat) (L' middle_init L_pre L_suf : List Nat) (v : Nat)
    (h_a_ge1 : a ≥ 1)
    (_h_e_ge1 : e ≥ 1)
    (_h_mi_ge1 : AllGe1 middle_init)
    (h_pre_one : ∀ x ∈ L_pre, x = 1)
    (hv : v ≥ 2)
    (h_eq : 1 :: middle_init.reverse ++ e :: (r' + 1) :: (a + 4) :: L'
           = L_pre ++ v :: L_suf) :
    -- Case 1: v sits within middle_init: middle_init = mi_A ++ v :: mi_B with
    -- mi_B all 1s. L_pre = 1 :: mi_B.reverse, L_suf = mi_A.reverse ++ tail.
    (∃ mi_A mi_B : List Nat, middle_init = mi_A ++ v :: mi_B ∧
       (∀ x ∈ mi_B, x = 1) ∧
       L_pre = 1 :: mi_B.reverse ∧
       L_suf = mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L') ∨
    -- Case 2: middle_init all 1s, v = e.
    ((∀ x ∈ middle_init, x = 1) ∧ e = v ∧
       L_pre = 1 :: middle_init.reverse ∧
       L_suf = (r' + 1) :: (a + 4) :: L') ∨
    -- Case 3: middle_init all 1s, e = 1, v = r' + 1.
    ((∀ x ∈ middle_init, x = 1) ∧ e = 1 ∧ r' + 1 = v ∧
       L_pre = 1 :: middle_init.reverse ++ [1] ∧
       L_suf = (a + 4) :: L') ∨
    -- Case 4: middle_init all 1s, e = 1, r' = 0, v = a + 4.
    ((∀ x ∈ middle_init, x = 1) ∧ e = 1 ∧ r' = 0 ∧ a + 4 = v ∧
       L_pre = 1 :: middle_init.reverse ++ [1, 1] ∧
       L_suf = L') := by
  -- L_pre starts with 1 (since LHS head is 1 and L_pre all 1s; if L_pre empty, v = 1 ⊥).
  cases L_pre with
  | nil =>
    rw [List.nil_append] at h_eq
    simp only [List.cons_append] at h_eq
    injection h_eq with h_head _
    omega
  | cons h_pre L_pre' =>
    have h_head : h_pre = 1 := h_pre_one h_pre List.mem_cons_self
    subst h_head
    simp only [List.cons_append] at h_eq
    injection h_eq with _ h_eq'
    have h_pre'_one : ∀ x ∈ L_pre', x = 1 :=
      fun x hx => h_pre_one x (List.mem_cons.mpr (Or.inr hx))
    -- List.append_eq_append_iff: ws ++ xs = ys ++ zs ↔
    --   (∃ as, ys = ws ++ as ∧ xs = as ++ zs) ∨ (∃ bs, ws = ys ++ bs ∧ zs = bs ++ xs)
    -- Here ws = middle_init.reverse, xs = e::rest, ys = L_pre', zs = v::L_suf.
    -- Disjunct 1: L_pre' = middle_init.reverse ++ as ∧ e::rest = as ++ v::L_suf.
    -- Disjunct 2: middle_init.reverse = L_pre' ++ bs ∧ v::L_suf = bs ++ e::rest.
    rcases List.append_eq_append_iff.mp h_eq' with
      ⟨k, h_pre_eq, h_tail⟩ | ⟨k, h_mi_eq, h_tail⟩
    · -- Disjunct 1: L_pre' = middle_init.reverse ++ k AND e :: rest = k ++ v :: L_suf.
      have h_mi_rev_one : ∀ x ∈ middle_init.reverse, x = 1 := by
        intro x hx
        have : x ∈ L_pre' := by rw [h_pre_eq]; exact List.mem_append_left _ hx
        exact h_pre'_one x this
      have h_mi_one : ∀ x ∈ middle_init, x = 1 := by
        intro x hx
        exact h_mi_rev_one x (List.mem_reverse.mpr hx)
      cases k with
      | nil =>
        -- e :: rest = [] ++ v :: L_suf = v :: L_suf. injection: e = v, rest = L_suf.
        rw [List.append_nil] at h_pre_eq
        rw [List.nil_append] at h_tail
        injection h_tail with hev_eq hLsuf_eq
        right; left
        refine ⟨h_mi_one, hev_eq, ?_, hLsuf_eq.symm⟩
        rw [h_pre_eq]
      | cons k_head k_tail =>
        simp only [List.cons_append] at h_tail
        injection h_tail with hk_head_eq h_tail2
        have h_kh_in : k_head ∈ L_pre' := by
          rw [h_pre_eq]; exact List.mem_append_right _ List.mem_cons_self
        have h_kh_eq_1 : k_head = 1 := h_pre'_one k_head h_kh_in
        -- hk_head_eq : e = k_head. h_kh_eq_1 : k_head = 1. Combine.
        have h_e_eq_1 : e = 1 := hk_head_eq.trans h_kh_eq_1
        cases k_tail with
        | nil =>
          rw [List.nil_append] at h_tail2
          injection h_tail2 with hrv_eq hLsuf_eq
          right; right; left
          refine ⟨h_mi_one, h_e_eq_1, hrv_eq, ?_, hLsuf_eq.symm⟩
          rw [h_pre_eq, h_kh_eq_1]
          simp
        | cons k_t_head k_t_tail =>
          simp only [List.cons_append] at h_tail2
          injection h_tail2 with hkth_eq h_tail3
          have h_kth_in : k_t_head ∈ L_pre' := by
            rw [h_pre_eq]
            exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr List.mem_cons_self))
          have h_kth_eq_1 : k_t_head = 1 := h_pre'_one k_t_head h_kth_in
          have h_r_eq_0 : r' = 0 := by
            -- hkth_eq : r' + 1 = k_t_head. h_kth_eq_1 : k_t_head = 1.
            have : r' + 1 = 1 := hkth_eq.trans h_kth_eq_1
            omega
          cases k_t_tail with
          | nil =>
            rw [List.nil_append] at h_tail3
            injection h_tail3 with hav_eq hLsuf_eq
            right; right; right
            refine ⟨h_mi_one, h_e_eq_1, h_r_eq_0, hav_eq, ?_, hLsuf_eq.symm⟩
            rw [h_pre_eq, h_kh_eq_1, h_kth_eq_1]
            simp
          | cons k_tt_head _ =>
            simp only [List.cons_append] at h_tail3
            injection h_tail3 with hktth_eq _
            have h_ktth_in : k_tt_head ∈ L_pre' := by
              rw [h_pre_eq]
              exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr
                (List.mem_cons.mpr (Or.inr List.mem_cons_self))))
            have h_ktth_eq_1 : k_tt_head = 1 := h_pre'_one k_tt_head h_ktth_in
            -- hktth_eq : a + 4 = k_tt_head. h_ktth_eq_1 : k_tt_head = 1.
            have : a + 4 = 1 := hktth_eq.trans h_ktth_eq_1
            omega
    · -- Disjunct 2: middle_init.reverse = L_pre' ++ k AND v :: L_suf = k ++ e :: rest.
      cases k with
      | nil =>
        -- middle_init.reverse = L_pre' (all 1s). v :: L_suf = e :: rest.
        rw [List.append_nil] at h_mi_eq
        rw [List.nil_append] at h_tail
        injection h_tail with hve_eq hLsuf_eq
        right; left
        have h_mi_rev_one : ∀ x ∈ middle_init.reverse, x = 1 := by
          intro x hx
          rw [h_mi_eq] at hx
          exact h_pre'_one x hx
        have h_mi_one : ∀ x ∈ middle_init, x = 1 := by
          intro x hx
          exact h_mi_rev_one x (List.mem_reverse.mpr hx)
        -- hve_eq : v = e. We need e = v.
        refine ⟨h_mi_one, hve_eq.symm, ?_, hLsuf_eq⟩
        rw [h_mi_eq]
      | cons k_head k_tail =>
        simp only [List.cons_append] at h_tail
        injection h_tail with hv_eq hLsuf_eq
        -- hv_eq : v = k_head, hLsuf_eq : L_suf = k_tail ++ e :: rest.
        left
        refine ⟨k_tail.reverse, L_pre'.reverse, ?_, ?_, ?_, ?_⟩
        · -- middle_init = k_tail.reverse ++ v :: L_pre'.reverse
          have h_rev := congrArg List.reverse h_mi_eq
          rw [List.reverse_reverse, List.reverse_append, List.reverse_cons] at h_rev
          -- h_rev : middle_init = k_tail.reverse ++ k_head :: L_pre'.reverse
          rw [h_rev, ← hv_eq]
          simp [List.append_assoc]
        · intro x hx
          exact h_pre'_one x (List.mem_reverse.mp hx)
        · rw [List.reverse_reverse]
        · rw [hLsuf_eq, List.reverse_reverse]

-- ============================================================
-- step_R3 4-case decomposition wrapper
-- ============================================================

/-- **Strengthened R3 closure**: like `thm_reach_multi_bounce_last_2_long_safe`,
    but the strict-safe disjunct is replaced with a 4-way structural decomposition
    of `(L_suf, v, R_out)` in terms of the predecessor's `(a, L', r', e, middle_init)`.
    Each case forces a specific `L_suf` shape in terms of `(a+4) :: L'` plus a prefix
    of `e, r'+1`, enabling phi+AllGe1 contradictions in cascade step_R3 branches.

    Cases:
    - **Case 1** (`v ∈ middle_init`): middle_init = mi_A ++ v :: mi_B, mi_B all 1s,
      L_suf = mi_A.reverse ++ e :: (r'+1) :: (a+4) :: L'.
    - **Case 2** (`v = e`): middle_init all 1s, L_suf = (r'+1) :: (a+4) :: L'.
    - **Case 3** (`v = r'+1`): middle_init all 1s, e = 1, L_suf = (a+4) :: L'.
    - **Case 4** (`v = a+4`): middle_init all 1s, e = 1, r' = 0, L_suf = L'.

    Note Cases 1, 2, 3 all force `(a+4) ∈ L_suf` (with a+4 ≥ 5 since a ≥ 1),
    while Case 4 has L_suf = L' (the original predecessor's L'). -/
theorem thm_reach_multi_bounce_last_2_long_4cases
    {a r' e : Nat} {L' middle_init : List Nat}
    (hinv : MacroInvariant
      (.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2]))) :
    ∃ (k : Nat) (L_suf : List Nat) (v : Nat) (R_out : List Nat), 0 < k ∧
      run sweeper
        (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k =
        (MacroConfig.M L_suf v R_out).toConfig ∧
      MacroInvariant (.M L_suf v R_out) ∧
      (∀ R, (MacroConfig.M L_suf v R_out) ≠ .M [] 3 R) ∧
      v ≥ 2 ∧
      ((∃ mi_A mi_B : List Nat, middle_init = mi_A ++ v :: mi_B ∧
          (∀ x ∈ mi_B, x = 1) ∧
          L_suf = mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L') ∨
       ((∀ x ∈ middle_init, x = 1) ∧ e = v ∧
          L_suf = (r' + 1) :: (a + 4) :: L') ∨
       ((∀ x ∈ middle_init, x = 1) ∧ e = 1 ∧ r' + 1 = v ∧
          L_suf = (a + 4) :: L') ∨
       ((∀ x ∈ middle_init, x = 1) ∧ e = 1 ∧ r' = 0 ∧ a + 4 = v ∧
          L_suf = L')) ∧
      (MacroConfig.M L_suf v R_out).phi =
        (MacroConfig.M0 (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])).phi + 2 := by
  -- Same setup as `thm_reach_multi_bounce_last_2_long_safe`.
  have hL := hinv.1
  have hR := hinv.2.1
  have ha : a ≥ 1 := (AllGe1_cons.mp hL).1
  have hL' : AllGe1 L' := (AllGe1_cons.mp hL).2
  have hR1 : AllGe1 ((r' + 3) :: e :: middle_init : List Nat) :=
    AllGe1_of_append_left hR
  have ⟨_, hR2⟩ := AllGe1_cons.mp hR1
  have ⟨he, h_mi_All⟩ := AllGe1_cons.mp hR2
  have h_mid : ∀ x ∈ ((e :: middle_init) ++ [1] : List Nat), x ≥ 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact he
      · exact AllGe1_mem h_mi_All hx
    · rcases List.mem_singleton.mp hx with rfl
      omega
  have h_in_eq : ((r' + 3) :: e :: middle_init ++ [1, 2] : List Nat) =
      (r' + 3) :: ((e :: middle_init) ++ [1]) ++ [0 + 2] := by
    simp [List.cons_append, List.append_assoc]
  have h_mb_raw := macro_multi_bounce_general a r' 0 L' ((e :: middle_init) ++ [1]) h_mid
  rw [← h_in_eq] at h_mb_raw
  set L_after : List Nat :=
    ((e :: middle_init) ++ [1]).reverse ++ (r' + 1) :: (a + 4) :: L' with hL_after_def
  have h_L_after_ge1 : AllGe1 L_after := by
    apply AllGe1_append
    · apply AllGe1_reverse
      apply AllGe1_append
      · exact AllGe1_cons.mpr ⟨he, h_mi_All⟩
      · exact AllGe1_singleton (by omega)
    · exact AllGe1_cons.mpr ⟨by omega, AllGe1_cons.mpr ⟨by omega, hL'⟩⟩
  have h_L_after_nonone : ∃ x ∈ L_after, x ≥ 2 := by
    refine ⟨a + 4, ?_, by omega⟩
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right
    exact List.mem_cons_self
  obtain ⟨k_shift, L_pre, v_out, L_suf, R_out, hk_shift, h_split, h_pre_one, hv_ge2,
          hrun_shift, hinv'_shift, hphi_shift⟩ :=
    shift_to_macro_prog_strong L_after [1]
      (List.cons_ne_nil _ _)
      (AllGe1_singleton (by omega))
      h_L_after_ge1 h_L_after_nonone
  -- Re-express L_after in canonical form for shift_inverse_4cases.
  have h_L_after_canonical : L_after
      = 1 :: middle_init.reverse ++ e :: (r' + 1) :: (a + 4) :: L' := by
    rw [hL_after_def]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append]
  -- h_split : L_after = L_pre ++ v_out :: L_suf.
  -- Combine with h_L_after_canonical to apply shift_inverse_4cases.
  have h_eq_for_inv : 1 :: middle_init.reverse ++ e :: (r' + 1) :: (a + 4) :: L'
                   = L_pre ++ v_out :: L_suf := by
    rw [← h_L_after_canonical]; exact h_split
  -- Apply the 4-case decomposition.
  have h_4cases_full := shift_inverse_4cases a r' e L' middle_init L_pre L_suf v_out
                       ha he h_mi_All h_pre_one hv_ge2 h_eq_for_inv
  -- Project out the L_pre information; keep only L_suf-related facts.
  have h_4cases :
      (∃ mi_A mi_B : List Nat, middle_init = mi_A ++ v_out :: mi_B ∧
          (∀ x ∈ mi_B, x = 1) ∧
          L_suf = mi_A.reverse ++ e :: (r' + 1) :: (a + 4) :: L') ∨
       ((∀ x ∈ middle_init, x = 1) ∧ e = v_out ∧
          L_suf = (r' + 1) :: (a + 4) :: L') ∨
       ((∀ x ∈ middle_init, x = 1) ∧ e = 1 ∧ r' + 1 = v_out ∧
          L_suf = (a + 4) :: L') ∨
       ((∀ x ∈ middle_init, x = 1) ∧ e = 1 ∧ r' = 0 ∧ a + 4 = v_out ∧
          L_suf = L') := by
    rcases h_4cases_full with ⟨mi_A, mi_B, hmi, hmi_one, _, hLsuf⟩ |
      ⟨h1, h2, _, h4⟩ | ⟨h1, h2, h3, _, h5⟩ | ⟨h1, h2, h3, h4, _, h6⟩
    · left; exact ⟨mi_A, mi_B, hmi, hmi_one, hLsuf⟩
    · right; left; exact ⟨h1, h2, h4⟩
    · right; right; left; exact ⟨h1, h2, h3, h5⟩
    · right; right; right; exact ⟨h1, h2, h3, h4, h6⟩
  -- Derive h_safe.
  have h_L_after_has_5 : ∃ x ∈ L_after, x ≥ 5 := by
    refine ⟨a + 4, ?_, by omega⟩
    apply List.mem_append.mpr; right
    apply List.mem_cons.mpr; right
    exact List.mem_cons_self
  have h_safe : ∀ R', (MacroConfig.M L_suf v_out R_out) ≠ .M [] 3 R' := by
    intro R' hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hLsuf, hv_eq, _⟩ := hcfg
    obtain ⟨x, hx, hx_ge5⟩ := h_L_after_has_5
    rw [h_split] at hx
    rcases List.mem_append.mp hx with hx_pre | hx_post
    · have := h_pre_one x hx_pre; omega
    · rcases List.mem_cons.mp hx_post with rfl | hx_suf
      · omega
      · rw [hLsuf] at hx_suf; exact List.not_mem_nil hx_suf
  -- Combine.
  obtain ⟨k_mb, h_mb⟩ : ∃ k_mb, run sweeper
      (M0_Config (a :: L') ((r' + 3) :: e :: middle_init ++ [1, 2])) k_mb =
        M_Config L_after (0 + 1) [1] :=
    ⟨_, h_mb_raw⟩
  refine ⟨k_mb + k_shift, L_suf, v_out, R_out, by omega, ?_, hinv'_shift,
          h_safe, hv_ge2, h_4cases, ?_⟩
  · rw [run_add, h_mb, hrun_shift, MacroConfig.toConfig_M]
  · rw [hphi_shift]
    simp only [hL_after_def, MacroConfig.phi_M, MacroConfig.phi_M0,
               List.sum_append, List.sum_cons, List.sum_nil,
               List.sum_reverse]
    omega

end Sweeper
