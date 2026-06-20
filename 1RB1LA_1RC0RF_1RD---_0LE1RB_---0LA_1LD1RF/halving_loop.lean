/-
**Halving-loop analysis** (Stage 0 of plan-next-route.md, 2026-06-10).

The orbit repeatedly visits left-empty configs `M([], c, R)`. For odd
`c ≥ 5` the dynamics is a deterministic "halving round":

    M([], c, d::R')  ↦  M([], (c-1)/2, 1 :: (d + (c-1)/2) :: R')

(one `sweep_left_empty`, then `(c-5)/2` sweeps, then one
`sweep_and_shift`). Iterating: `c+1` halves each round while `c` stays
odd. Writing `c + 1 = 2^v · m` with `m` odd:

  * if `m ≥ 3` the chain exits at the even cursor `m - 1` (safe);
  * if `m = 1` (i.e. `c+1` is a power of two) the chain reaches
    `M([], 3, ·)`, which HALTS in 31 raw steps (`halt_M_empty_3`,
    proved below — this also witnesses that axiom `reach_M_nil_3`
    cannot be a *progress* fact; only unreachability can close R1).

Hence the entire R1 obligation reduces to the arithmetic kernel
`HalvingKernel`: no reachable left-empty odd-cursor config has
`c + 1` a power of two. `not_M_empty_3_of_kernel` makes the reduction
formal. Empirically (60 M macro steps): ν₂(c+1) at entries reaches 11
with a geometric tail — the kernel is Collatz-like, not finite-state.

This file adds NO axioms and NO sorries.
-/
import progress

namespace Sweeper

open BusyLean

/-- `n` is a power of two. -/
def IsPow2 (n : Nat) : Prop := ∃ v : Nat, n = 2 ^ v

-- ============================================================
-- The doom base case: M([], 3, d::R') halts in 31 raw steps.
-- The head never enters the R region, so the count is uniform in R'.
-- ============================================================

theorem halt_M_empty_3 (d : Nat) (R' : List Nat) :
    (run sweeper (M_Config [] 3 (d :: R')) 31).state = none := by
  simp (config := { decide := true }) [run, step, sweeper, ones]

-- ============================================================
-- The sweep phase: n sweeps from cursor 2n+3 down to cursor 3,
-- growing the L-head and R-head by n.
-- ============================================================

theorem sweeps_phase (n : Nat) (a d : Nat) (L R : List Nat) :
    ∃ N : Nat, run sweeper (M_Config ((a + 1) :: L) (2 * n + 3) ((d + 1) :: R)) N
      = M_Config ((a + n + 1) :: L) 3 ((d + n + 1) :: R) := by
  induction n generalizing a d with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih (a + 1) (d + 1)
    refine ⟨(2 * (2 * n + 2 + 3) + 7) + N, ?_⟩
    rw [show 2 * (n + 1) + 3 = 2 * n + 2 + 3 from by omega, run_add,
      macro_sweep (a + 1) (2 * n + 2) (d + 1) L R,
      show 2 * n + 2 + 1 = 2 * n + 3 from by omega, hN,
      show a + 1 + n + 1 = a + (n + 1) + 1 from by omega,
      show d + 1 + n + 1 = d + (n + 1) + 1 from by omega]

-- ============================================================
-- One full halving round: M([], 2k+5, d::R') ↦ M([], k+2, 1::(d+k+2)::R').
-- In cursor terms: odd c ≥ 5 goes to (c-1)/2, i.e. c+1 halves.
-- ============================================================

theorem halving_round (k d : Nat) (R' : List Nat) :
    ∃ N : Nat, 0 < N ∧
      run sweeper (M_Config [] (2 * k + 5) (d :: R')) N
        = M_Config [] (k + 2) (1 :: (d + k + 2) :: R') := by
  obtain ⟨N₁, hN₁⟩ := sweeps_phase k 0 d ([] : List Nat) R'
  simp only [Nat.zero_add] at hN₁
  refine ⟨(2 * (2 * k + 2 + 3) + 7) + N₁ + 19, by omega, ?_⟩
  rw [show 2 * k + 5 = 2 * k + 2 + 3 from by omega, run_add, run_add,
    macro_sweep_left_empty (2 * k + 2) d R',
    show 2 * k + 2 + 1 = 2 * k + 3 from by omega, hN₁,
    macro_sweep_and_shift (k + 1) (d + k + 1) [] R',
    show k + 1 + 1 = k + 2 from by omega,
    show d + k + 1 + 1 = d + k + 2 from by omega]

-- ============================================================
-- Doom: if c + 1 = 2^v (v ≥ 2), the run from M([], c, d::R') halts.
-- ============================================================

theorem doom_mersenne : ∀ v : Nat, 2 ≤ v → ∀ (d : Nat) (R' : List Nat),
    ∃ n : Nat, (run sweeper (M_Config [] (2 ^ v - 1) (d :: R')) n).state = none := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ v ih =>
    intro hv d R'
    by_cases hv2 : v < 2
    · -- v = 1: cursor 2^2 - 1 = 3, direct halt.
      have hv1 : v = 1 := by omega
      subst hv1
      refine ⟨31, ?_⟩
      rw [show (2 : Nat) ^ (1 + 1) - 1 = 3 from by norm_num]
      exact halt_M_empty_3 d R'
    · -- v ≥ 2: one halving round, then induction.
      push_neg at hv2
      have h4 : 4 ≤ 2 ^ v := by
        calc (4 : Nat) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by omega) hv2
      have hpow : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [pow_succ]; omega
      have hk : 2 ^ (v + 1) - 1 = 2 * (2 ^ v - 3) + 5 := by omega
      obtain ⟨N, _, hN⟩ := halving_round (2 ^ v - 3) d R'
      obtain ⟨n, hn⟩ := ih hv2 1 ((d + (2 ^ v - 3) + 2) :: R')
      refine ⟨N + n, ?_⟩
      rw [run_add, hk, hN, show 2 ^ v - 3 + 2 = 2 ^ v - 1 from by omega]
      exact hn

-- ============================================================
-- The isolated arithmetic kernel, and the formal reduction.
-- ============================================================

/-- **The kernel**: no reachable left-empty odd-cursor macro config has
    `c + 1` a power of two. Empirically validated through 6.2 × 10¹⁶ raw
    steps (ν₂(c+1) ≤ 11 over 60 M macro steps, geometric tail). By
    `doom_mersenne` this is NECESSARY for non-halting; by
    `not_M_empty_3_of_kernel` below it subsumes the R1 obligation. -/
def HalvingKernel : Prop :=
  ∀ (c : Nat) (R : List Nat), OrbitReachable (.M [] c R) →
    c % 2 = 1 → ¬ IsPow2 (c + 1)

/-- The kernel subsumes the R1 unreachability obligation: if no reachable
    left-empty odd config has `c+1` a power of two, then in particular
    `M([], 3, R)` (where `c + 1 = 4 = 2²`) is unreachable. -/
theorem not_M_empty_3_of_kernel (H : HalvingKernel) :
    ∀ {cfg : MacroConfig}, OrbitReachable cfg → ∀ R : List Nat, cfg ≠ .M [] 3 R := by
  intro cfg hreach R hcfg
  subst hcfg
  exact H 3 R hreach (by omega) ⟨2, rfl⟩

-- ============================================================
-- Raw-run certificates: every OrbitReachable config is actually
-- reached by the raw TM from the blank tape.
-- ============================================================

theorem OrbitReachable.toRun {cfg : MacroConfig} (h : OrbitReachable cfg) :
    ∃ n : Nat, run sweeper (initConfig 6) n = cfg.toConfig := by
  induction h with
  | init => exact ⟨43, init_to_macro⟩
  | @step_macro cfg cfg' k h_prev h_step ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + k, ?_⟩
      rw [run_add, hn]
      exact (macroStep_sound _ _ _ h_step h_prev.macroInvariant).1
  | @step_multi_bounce_general a r' last'' L' R_mid h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      have hR : ∀ x ∈ R_mid, x ≥ 1 := fun x hx =>
        AllGe1_mem h_prev.macroInvariant.2.1
          (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      refine ⟨n + (r' + (last'' + 1) + 3 * R_mid.length + List.sum R_mid + 17), ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      have hcert := macro_multi_bounce_general a r' (last'' + 1) L' R_mid hR
      rw [show last'' + 1 + 2 = last'' + 3 from by omega,
        show last'' + 1 + 1 = last'' + 2 from by omega] at hcert
      exact hcert
  | @step_multi_bounce_general_to_zero a r' L' R_mid h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      have hR : ∀ x ∈ R_mid, x ≥ 1 := fun x hx =>
        AllGe1_mem h_prev.macroInvariant.2.1
          (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      refine ⟨n + (r' + 3 * R_mid.length + List.sum R_mid + 16), ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0]
      exact macro_multi_bounce_general_to_zero a r' L' R_mid hR
  | @step_multi_bounce_2_and_shift a r L' h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + (r + 24), ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      exact macro_multi_bounce_2_and_shift a r L'
  | @step_multi_bounce_2_double_shift a L' h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 29, ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      exact macro_multi_bounce_2_double_shift a L'
  | @step_multi_bounce_3run_last_2 a r' e L' h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + (r' + 3 * 1 + (e + 2) + 17 + 6), ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      exact macro_multi_bounce_3run_last_2 a r' e L'
  | @step_multi_bounce_last_2_general a r' m_last L' middle_init h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      have h_init : ∀ x ∈ middle_init, x ≥ 1 := fun x hx =>
        AllGe1_mem h_prev.macroInvariant.2.1
          (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      refine ⟨n + (r' + 3 * (middle_init.length + 1) +
        (middle_init.sum + (m_last + 2)) + 17 + 6), ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      exact macro_multi_bounce_last_2_general a r' m_last L' middle_init h_init
  | @step_R2_zero a L' h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 39, ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      exact bridge_R2_zero a L'
  | @step_R2_succ a r L' h_prev ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + (r + 34), ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0, MacroConfig.toConfig_M]
      exact bridge_R2_pos a r L'
  | @step_R3 a r' e L' middle_init cfg' k h_prev h_run h_inv h_k h_ne h_4c h_phi ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + k, ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M0]
      exact h_run
  | @step_R1 d R' cfg' k h_prev h_run h_inv h_k h_phi ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + k, ?_⟩
      rw [run_add, hn]
      simp only [MacroConfig.toConfig_M]
      exact h_run

-- ============================================================
-- The equivalence: never-halting ⟺ HalvingKernel.
-- ============================================================

/-- Axiom-free progress from the kernel: instantiate `orbit_progress_param`
    with the kernel-derived unreachability of the R1 shape. -/
theorem orbit_progress_kernel (H : HalvingKernel) (c : Config 6) (h : OrbitProg c) :
    ∃ k, 0 < k ∧ OrbitProg (run sweeper c k) ∧ (run sweeper c k).state ≠ none :=
  orbit_progress_param
    (fun _hinv hreach => absurd rfl (not_M_empty_3_of_kernel H hreach _)) c h

/-- **Kernel ⟹ non-halting**, with no appeal to `reach_M_nil_3`. -/
theorem sweeper_never_halts_of_kernel (H : HalvingKernel) (k : Nat) :
    (run sweeper (initConfig 6) k).state ≠ none := by
  suffices h43 : ∀ j, j < 43 → (run sweeper (initConfig 6) j).state ≠ none by
    by_cases hk : k < 43
    · exact h43 k hk
    · push_neg at hk
      rw [show k = 43 + (k - 43) from by omega, run_add]
      exact nonhalt_of_progress sweeper OrbitProg (orbit_progress_kernel H)
        (run sweeper (initConfig 6) 43) init_orbit_prog (k - 43)
  intro j hj
  interval_cases j <;> simp [run, step, sweeper, initConfig]

/-- **Non-halting ⟹ kernel**: a reachable left-empty config with
    `c + 1 = 2^v` would, by `toRun` + `doom_mersenne`, make the machine
    halt. -/
theorem kernel_of_never_halts
    (NH : ∀ k, (run sweeper (initConfig 6) k).state ≠ none) : HalvingKernel := by
  intro c R hreach hodd hpow
  obtain ⟨v, hv⟩ := hpow
  have hinv := hreach.macroInvariant
  have hc2 : c ≥ 2 := hinv.2.1
  have hR_ne : R ≠ [] := hinv.2.2.2
  obtain ⟨d, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
  have hv2 : 2 ≤ v := by
    by_contra hlt
    push_neg at hlt
    have h2 : 2 ^ v ≤ 2 := by
      calc 2 ^ v ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 := by norm_num
    omega
  obtain ⟨n, hn⟩ := hreach.toRun
  obtain ⟨m, hm⟩ := doom_mersenne v hv2 d R'
  apply NH (n + m)
  rw [run_add, hn, MacroConfig.toConfig_M, show c = 2 ^ v - 1 from by omega]
  exact hm

/-- **THE EQUIVALENCE** (kernel-checked, no custom axioms, no sorries):
    the sweeper runs forever from the blank tape **iff** no reachable
    left-empty odd-cursor macro config has `c + 1` a power of two. -/
theorem never_halts_iff_kernel :
    (∀ k, (run sweeper (initConfig 6) k).state ≠ none) ↔ HalvingKernel :=
  ⟨kernel_of_never_halts, fun H k => sweeper_never_halts_of_kernel H k⟩

end Sweeper
