/-
Era-graded analysis for closing R1 (Strategy B of plan-r1.md).

This file develops era-graded structures: an `EraStartConfig` capturing
era-boundary shapes, and a structural lemma showing that intra-era sweep
transitions preserve `L ≠ []`.

Era state. Every era boundary observed empirically has shape
`M(L, c, [1])` with `L ≠ []` and `c ≥ 4` (era_findings.md, 63 K boundaries).
Within an era, repeated `macro_sweep` decrements `c` by 2 each step while
prepending +1 to `L[0]` and `R[0]`. No sweep rule shrinks `L`.

Strategy. Closing the only remaining custom axiom `reach_M_nil_3` (R1)
requires proving `OrbitReachable (.M [] 3 (d :: R')) → False`. The
era-graded path proves the stronger structural claim `reachable ∧ c = 3
→ L ≠ []`. The non-shrinking property of intra-era sweeps proved here
is the foundation for that lift.
-/

import progress

namespace Sweeper

open BusyLean

-- ============================================================
-- Era-start configurations
-- ============================================================

/-- Era-start shape: `M(L, c, [1])` with `L` non-empty, all run-lengths ≥ 1,
    and cursor `c ≥ 4` (empirical era-boundary form). -/
structure EraStartConfig where
  L : List Nat
  c : Nat
  L_ne_nil : L ≠ []
  L_all_ge1 : AllGe1 L
  c_ge4 : c ≥ 4

/-- Embed an `EraStartConfig` into a `MacroConfig` (the `M` shape with `R = [1]`). -/
def EraStartConfig.toMacro (e : EraStartConfig) : MacroConfig :=
  .M e.L e.c [1]

/-- Every era-start shape satisfies the macro invariant. -/
theorem EraStartConfig.macroInvariant (e : EraStartConfig) :
    MacroInvariant e.toMacro := by
  refine ⟨e.L_all_ge1, ?_, ?_, ?_⟩
  · have := e.c_ge4; omega
  · exact AllGe1_singleton (by omega)
  · exact List.cons_ne_nil _ _

/-- The initial macro state `M([1], 4, [1])` is an `EraStartConfig`. -/
def EraStartConfig.init : EraStartConfig where
  L := [1]
  c := 4
  L_ne_nil := List.cons_ne_nil _ _
  L_all_ge1 := AllGe1_singleton (by omega)
  c_ge4 := by omega

@[simp] theorem EraStartConfig.init_toMacro :
    EraStartConfig.init.toMacro = .M [1] 4 [1] := rfl

-- ============================================================
-- Intra-era sweeps preserve L ≠ []
-- ============================================================

/-- Single intra-era sweep on non-empty `L` preserves `L ≠ []`.
    `macroStep` on `M(a :: L', c+4, d :: R')` outputs
    `M((a+1) :: L', c+2, (d+1) :: R')`; the leading `a+1` keeps `L` non-empty. -/
theorem macroStep_M_sweep_cons_preserves_L_ne_nil
    {a : Nat} {L' : List Nat} {c : Nat} {d : Nat} {R' : List Nat}
    (hc : c ≥ 4) {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M (a :: L') c (d :: R')) = some (k, cfg')) :
    ∃ a' L'' c' d' R'', cfg' = .M (a' :: L'') c' (d' :: R'') := by
  obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 4 := ⟨c - 4, by omega⟩
  ms_simp at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  exact ⟨a + 1, L', c'' + 2, d + 1, R', rfl⟩

/-- Single intra-era sweep on empty `L` produces `L = [1]`.
    `macroStep` on `M([], c+4, d :: R')` outputs `M([1], c+2, (d+1) :: R')`. -/
theorem macroStep_M_sweep_left_empty_produces_one
    {c : Nat} {d : Nat} {R' : List Nat}
    (hc : c ≥ 4) {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M [] c (d :: R')) = some (k, cfg')) :
    ∃ c' d' R'', cfg' = .M [1] c' (d' :: R'') := by
  obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 4 := ⟨c - 4, by omega⟩
  ms_simp at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  exact ⟨c'' + 2, d + 1, R', rfl⟩

/-- **Main intra-era sweep lemma**: for any input `M(L, c, R)` with `c ≥ 4`
    and `R ≠ []`, the sole `macroStep` dispatch is a sweep variant whose
    output is again `M` with `L ≠ []`.

    This is the structural foundation of Strategy B: within an era's
    sweep prefix (`c` decrementing from era-start value down to `c ∈ {2, 3}`),
    every transition keeps the macro shape an `M` with non-empty `L`. -/
theorem macroStep_M_intra_era_preserves_L_ne_nil
    {L : List Nat} {c : Nat} {R : List Nat}
    (hc : c ≥ 4) (hR : R ≠ [])
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M L c R) = some (k, cfg')) :
    ∃ L' c' R', cfg' = .M L' c' R' ∧ L' ≠ [] := by
  obtain ⟨d, R', rfl⟩ := List.exists_cons_of_ne_nil hR
  cases L with
  | nil =>
    obtain ⟨c', d', R'', heq⟩ := macroStep_M_sweep_left_empty_produces_one hc hstep
    exact ⟨[1], c', d' :: R'', heq, List.cons_ne_nil _ _⟩
  | cons a L' =>
    obtain ⟨a', L'', c', d', R'', heq⟩ := macroStep_M_sweep_cons_preserves_L_ne_nil hc hstep
    exact ⟨a' :: L'', c', d' :: R'', heq, List.cons_ne_nil _ _⟩

-- ============================================================
-- Era-exit transitions (c = 2 sweep_to_zero, c = 3 sweep_and_shift)
-- ============================================================

/-- Era exit at `c = 2` (sweep_to_zero): input `M(a :: L', 2, d :: R')`
    produces `M0((a+1) :: L', (d+1) :: R')` — the M0 phase with non-empty L. -/
theorem macroStep_M_c2_output
    {a : Nat} {L' : List Nat} {d : Nat} {R' : List Nat}
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M (a :: L') 2 (d :: R')) = some (k, cfg')) :
    cfg' = .M0 ((a + 1) :: L') ((d + 1) :: R') := by
  ms_simp at hstep
  obtain ⟨_, rfl⟩ := hstep; rfl

/-- Era exit at `c = 3` (sweep_and_shift): input `M(a :: L', 3, d :: R')`
    produces `M(L', a+1, 1 :: (d+1) :: R')`. The output `L = L'` may be
    empty if the input had `L = [a]` (singleton). This is the only macro
    rule that shrinks `L`. -/
theorem macroStep_M_c3_output
    {a : Nat} {L' : List Nat} {d : Nat} {R' : List Nat}
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M (a :: L') 3 (d :: R')) = some (k, cfg')) :
    cfg' = .M L' (a + 1) (1 :: (d + 1) :: R') := by
  ms_simp at hstep
  obtain ⟨_, rfl⟩ := hstep; rfl

/-- At `c = 3` with `|L| ≥ 2`, the output `L` (= input's tail) is still
    non-empty. This is the per-step preservation needed to lift `L ≠ []`
    across an entire era when `|L_initial| ≥ 2`. -/
theorem macroStep_M_c3_L_ge2_preserves_L_ne_nil
    {a b : Nat} {L'' : List Nat} {d : Nat} {R' : List Nat}
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M (a :: b :: L'') 3 (d :: R')) = some (k, cfg')) :
    ∃ L₂ c₂ R₂, cfg' = .M L₂ c₂ R₂ ∧ L₂ ≠ [] :=
  ⟨b :: L'', a + 1, 1 :: (d + 1) :: R',
   macroStep_M_c3_output hstep, List.cons_ne_nil _ _⟩

/-- The boundary case at `c = 3` with `|L| = 1` (singleton): output `L = []`.
    This is the unique macroStep that produces an `L = []` shape; it is the
    only "internal" generator of `M(_, _, _)` configs that R1 could trigger
    on. Strategy B's task is to show no orbit-reachable singleton-L `c = 3`
    config exists (or its post-image avoids `c = 3` recurrence). -/
theorem macroStep_M_c3_L_singleton_drains
    {a d : Nat} {R' : List Nat}
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M [a] 3 (d :: R')) = some (k, cfg')) :
    cfg' = .M [] (a + 1) (1 :: (d + 1) :: R') :=
  macroStep_M_c3_output hstep

-- ============================================================
-- Iterated intra-era sweep (sweep prefix from era-start)
-- ============================================================

/-- Iterated `macroStep` over the sweep prefix. Starting from
    `M(a :: L', c + 4, d :: R')`, after one `macroStep` we land at
    `M((a+1) :: L', c + 2, (d+1) :: R')`. Repeated `n` times this is
    `M((a + n) :: L', (c + 4) - 2n, …)` so long as `n ≤ c/2 + 1`.

    We state the `n`-step result via `macroEra` since it already iterates
    `macroStep` and tracks raw-TM equivalence. Within the sweep prefix
    `c ≥ 4`, every step is a sweep; after exactly `(c-2)/2` (even c) or
    `(c-3)/2` (odd c) steps, the cursor enters `{2, 3}` and dispatch
    switches to era-exit rules. -/
theorem macroStep_M_sweep_cons_full_output
    (a : Nat) (L' : List Nat) (c : Nat) (d : Nat) (R' : List Nat) :
    macroStep (.M (a :: L') (c + 4) (d :: R')) =
      some (2 * (c + 4) + 7, .M ((a + 1) :: L') (c + 2) ((d + 1) :: R')) := by
  rfl

/-- Iterated sweep on a non-empty `L`: `n` consecutive sweeps from
    `M(a :: L', c + 4 + 2n, d :: R')` produce
    `M((a + n + 1) :: L', c + 2, (d + n + 1) :: R')`.
    Proven by induction on `n` using `macroStep_M_sweep_cons_full_output`. -/
theorem sweep_iter_M_cons_output
    (n : Nat) (a : Nat) (L' : List Nat) (c d : Nat) (R' : List Nat) :
    (Sweeper.macroEra (n + 1) (.M (a :: L') (c + 4 + 2 * n) (d :: R'))).2 =
    .M ((a + n + 1) :: L') (c + 2) ((d + n + 1) :: R') := by
  induction n generalizing a c d with
  | zero =>
    simp only [Sweeper.macroEra, Nat.mul_zero, Nat.add_zero,
               macroStep_M_sweep_cons_full_output]
  | succ n ih =>
    -- After one step: M((a+1) :: L', c + 4 + 2n, (d+1) :: R')
    -- Then n more steps via `ih` lands at the target.
    have hstep := macroStep_M_sweep_cons_full_output a L' (c + 2 * (n + 1)) d R'
    have hc_eq : c + 4 + 2 * (n + 1) = c + 2 * (n + 1) + 4 := by ring
    rw [hc_eq]
    simp only [Sweeper.macroEra, hstep]
    have hih := ih (a + 1) (c) (d + 1)
    have hc_eq2 : c + 4 + 2 * n = (c + 2 * (n + 1)) + 2 := by ring
    rw [hc_eq2] at hih
    have htarget : a + 1 + n + 1 = a + (n + 1) + 1 := by ring
    have htarget' : d + 1 + n + 1 = d + (n + 1) + 1 := by ring
    rw [htarget, htarget'] at hih
    convert hih using 2

-- ============================================================
-- Era-boundary transitions: M0 with R = [1] → next era-start
-- ============================================================

/-- Era boundary, multi-element M0: `M0((a+1) :: b :: L'', [1])` produces
    era-start `M((b+1) :: L'', a+4, [1])`. -/
theorem macroStep_M0_era_and_sweep_output
    {a b : Nat} {L'' : List Nat}
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M0 ((a + 1) :: b :: L'') [1]) = some (k, cfg')) :
    cfg' = .M ((b + 1) :: L'') (a + 4) [1] := by
  ms_simp at hstep
  obtain ⟨_, rfl⟩ := hstep; rfl

/-- Era boundary, singleton M0: `M0([a+1], [1])` produces era-start
    `M([1], a+4, [1])`. -/
theorem macroStep_M0_era_and_sweep_solo_output
    {a : Nat}
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M0 [a + 1] [1]) = some (k, cfg')) :
    cfg' = .M [1] (a + 4) [1] := by
  ms_simp at hstep
  obtain ⟨_, rfl⟩ := hstep; rfl

/-- Either era-boundary M0 dispatch produces an `EraStartConfig`-shaped output.
    This is the "post-era-end → next era-start" statement: any `M0(L, [1])`
    satisfying the macro invariant precondition that lands in the macroStep
    dispatch produces an era-start shape. -/
theorem macroStep_M0_R1_produces_era_start
    {L : List Nat} (hL : AllGe1 L) (hL_ne : L ≠ [])
    {k : Nat} {cfg' : MacroConfig}
    (hstep : macroStep (.M0 L [1]) = some (k, cfg')) :
    ∃ e : EraStartConfig, cfg' = e.toMacro := by
  obtain ⟨a', L_rest, rfl⟩ := List.exists_cons_of_ne_nil hL_ne
  have ha' := (AllGe1_cons.mp hL).1
  have hL_rest := (AllGe1_cons.mp hL).2
  obtain ⟨a, rfl⟩ : ∃ a, a' = a + 1 := ⟨a' - 1, by omega⟩
  cases L_rest with
  | nil =>
    have h := macroStep_M0_era_and_sweep_solo_output hstep
    refine ⟨{ L := [1], c := a + 4,
              L_ne_nil := List.cons_ne_nil _ _,
              L_all_ge1 := AllGe1_singleton (by omega),
              c_ge4 := by omega }, ?_⟩
    rw [h]; rfl
  | cons b L'' =>
    have h := macroStep_M0_era_and_sweep_output hstep
    have hb : b ≥ 1 := (AllGe1_cons.mp hL_rest).1
    have hL'' : AllGe1 L'' := (AllGe1_cons.mp hL_rest).2
    refine ⟨{ L := (b + 1) :: L'', c := a + 4,
              L_ne_nil := List.cons_ne_nil _ _,
              L_all_ge1 := AllGe1_cons.mpr ⟨by omega, hL''⟩,
              c_ge4 := by omega }, ?_⟩
    rw [h]; rfl

-- ============================================================
-- IntraEra: within-era trajectory invariant
-- ============================================================

/-- The within-era trajectory invariant. Inductively defined as the
    closure of `EraStartConfig.toMacro` under `macroStep`, excluding
    transitions whose target is the next era-start (an M-shape with
    `R = [1]`).

    Reading: every `IntraEra cfg` config sits inside one specific era's
    trajectory — either at the era-start, or at some intermediate point
    reached from the era-start by macroStep iterations that haven't yet
    produced a fresh `M(_, _, [1])` shape.

    The boundary condition `¬ ∃ L c, cfg' = .M L c [1]` cleanly stops
    the closure at the next era's beginning, which would re-enter
    `IntraEra` via the `era_start` constructor (with a different
    `EraStartConfig` witness). -/
inductive IntraEra : MacroConfig → Prop where
  | era_start (e : EraStartConfig) : IntraEra e.toMacro
  | step_within {cfg cfg' : MacroConfig} {k : Nat} :
      IntraEra cfg → macroStep cfg = some (k, cfg') →
      (¬ ∃ L c, cfg' = .M L c [1]) →
      IntraEra cfg'

/-- Every `IntraEra` config satisfies `MacroInvariant`. -/
theorem IntraEra.macroInvariant {cfg : MacroConfig} (h : IntraEra cfg) :
    MacroInvariant cfg := by
  induction h with
  | era_start e => exact e.macroInvariant
  | step_within _ hstep _ ih => exact (macroStep_sound _ _ _ hstep ih).2.1

/-- An `IntraEra` config with shape `M(_, _, [1])` must be the era-start
    of its era. The step constructor explicitly excludes producing this
    shape, so only the `era_start` constructor can introduce it. -/
theorem IntraEra.M_R_one_is_era_start
    {cfg : MacroConfig} {L : List Nat} {c : Nat}
    (h : IntraEra cfg) (hcfg : cfg = .M L c [1]) :
    ∃ e : EraStartConfig, cfg = e.toMacro := by
  cases h with
  | era_start e => exact ⟨e, rfl⟩
  | step_within _ _ hnot =>
    exact absurd ⟨L, c, hcfg⟩ hnot

/-- An `IntraEra` config with shape `M(_, _, [1])` has non-empty `L`,
    `AllGe1 L`, and `c ≥ 4`. Inherits the era-start constraints. -/
theorem IntraEra.M_R_one_constraints
    {cfg : MacroConfig} {L : List Nat} {c : Nat}
    (h : IntraEra cfg) (hcfg : cfg = .M L c [1]) :
    L ≠ [] ∧ AllGe1 L ∧ c ≥ 4 := by
  obtain ⟨e, he⟩ := h.M_R_one_is_era_start hcfg
  rw [hcfg, EraStartConfig.toMacro, MacroConfig.M.injEq] at he
  obtain ⟨hL, hc, _⟩ := he
  exact ⟨hL ▸ e.L_ne_nil, hL ▸ e.L_all_ge1, hc ▸ e.c_ge4⟩

/-- The orbit's initial macro state is `IntraEra`. -/
theorem IntraEra.init : IntraEra (.M [1] 4 [1]) := by
  have : EraStartConfig.init.toMacro = .M [1] 4 [1] := rfl
  exact this ▸ IntraEra.era_start EraStartConfig.init

-- ============================================================
-- IntraEraOf: era-graded refinement of IntraEra
-- ============================================================
-- `IntraEraOf e cfg` is the parameterized version of `IntraEra cfg` that
-- tracks the seeding era-start `e`. This is required for Stage D-style
-- characterizations that relate `cfg`'s shape to `e`'s structure.
--
-- Bridge lemmas: `IntraEraOf.toIntraEra` (forward) and
-- `IntraEra.exists_intraEraOf` (backward) establish the equivalence
-- `IntraEra cfg ↔ ∃ e, IntraEraOf e cfg`.

/-- Era-graded intra-era trajectory: configs reachable from a specific
    era-start `e` by macroStep iterations that don't produce a fresh
    era-shape `M(_, _, [1])` along the way. -/
inductive IntraEraOf (e : EraStartConfig) : MacroConfig → Prop where
  | era_start : IntraEraOf e e.toMacro
  | step_within {cfg cfg' : MacroConfig} {k : Nat} :
      IntraEraOf e cfg → macroStep cfg = some (k, cfg') →
      (¬ ∃ L c, cfg' = .M L c [1]) →
      IntraEraOf e cfg'

/-- Forward bridge: every `IntraEraOf e cfg` is also `IntraEra cfg`. -/
theorem IntraEraOf.toIntraEra {e : EraStartConfig} {cfg : MacroConfig}
    (h : IntraEraOf e cfg) : IntraEra cfg := by
  induction h with
  | era_start => exact IntraEra.era_start e
  | step_within _ hstep hnot ih => exact IntraEra.step_within ih hstep hnot

/-- Backward bridge: every `IntraEra cfg` arises from some era-start. -/
theorem IntraEra.exists_intraEraOf {cfg : MacroConfig} (h : IntraEra cfg) :
    ∃ e : EraStartConfig, IntraEraOf e cfg := by
  induction h with
  | era_start e => exact ⟨e, IntraEraOf.era_start⟩
  | step_within _ hstep hnot ih =>
    obtain ⟨e, h_e⟩ := ih
    exact ⟨e, IntraEraOf.step_within h_e hstep hnot⟩

/-- Every `IntraEraOf e cfg` config satisfies `MacroInvariant`.
    Inherited from the era-start's invariant via macroStep_sound. -/
theorem IntraEraOf.macroInvariant {e : EraStartConfig} {cfg : MacroConfig}
    (h : IntraEraOf e cfg) : MacroInvariant cfg :=
  h.toIntraEra.macroInvariant

/-- An `IntraEraOf e cfg` config with shape `M(_, _, [1])` must equal
    `e.toMacro`. The step constructor's `hnot` excludes producing this
    shape, so only the `era_start` constructor introduces it. -/
theorem IntraEraOf.M_R_one_is_era_start
    {e : EraStartConfig} {cfg : MacroConfig} {L : List Nat} {c : Nat}
    (h : IntraEraOf e cfg) (hcfg : cfg = .M L c [1]) :
    cfg = e.toMacro := by
  cases h with
  | era_start => rfl
  | step_within _ _ hnot => exact absurd ⟨L, c, hcfg⟩ hnot

-- ============================================================
-- Structural exclusion: M([], 3, [d]) is not reachable in IntraEra
-- ============================================================
-- The full goal `IntraEra cfg → cfg ≠ M([], 3, R)` is FALSE for arbitrary
-- R: from the era-start `M([1], 5, [1])` (valid `EraStartConfig`), the
-- trajectory M([1], 5, [1]) → M([2], 3, [2]) → M([], 3, [1, 3]) reaches
-- the R1 shape with R = [1, 3] (length ≥ 2). Excluding M([1], 5, [1])
-- requires cascade-style analysis on orbit-reachable era-starts (the
-- `OrbitReachable` lift in plan-r1.md's Strategy B step 3).
--
-- What IS provable from IntraEra alone is the **single-element R case**:
-- no IntraEra config has shape M([], 3, [d]) for any d. This handles the
-- R1 axiom shape `M [] 3 (d :: R')` when R' = []. The R' ≠ [] case
-- requires more.

/-- No `macroStep` transition produces output `M([], 3, [d])` from any
    `MacroInvariant`-respecting input. The proof is an exhaustive case
    split on the macroStep dispatch tree; in every case the output shape
    differs from the target by a structural mismatch (kind, list length,
    or cursor arithmetic). -/
theorem macroStep_no_M_empty_3_single
    {cfg : MacroConfig} {k : Nat} {d : Nat}
    (hinv : MacroInvariant cfg)
    (hstep : macroStep cfg = some (k, .M [] 3 [d])) : False := by
  cases cfg with
  | M L c R =>
    have hc := hinv.2.1
    have hR_ne := hinv.2.2.2
    obtain ⟨d', R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    cases L with
    | nil =>
      match c, hc with
      | 2, _ => ms_done at hstep
      | 3, _ => ms_done at hstep
      | c' + 4, _ => ms_done at hstep
    | cons a L' =>
      match c, hc with
      | 2, _ => ms_done at hstep
      | 3, _ => ms_done at hstep
      | c' + 4, _ => ms_done at hstep
  | M0 L R =>
    have hL := hinv.1; have hR := hinv.2.1
    have hL_ne := hinv.2.2.1; have hR_ne := hinv.2.2.2.1
    have hNH := hinv.2.2.2.2
    obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL_ne
    obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hR_ne
    have ha := (AllGe1_cons.mp hL).1
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    cases R' with
    | nil =>
      have hr := (AllGe1_cons.mp hR).1
      match r, hr with
      | 1, _ =>
        cases L' with
        | nil => ms_done at hstep
        | cons b L'' => ms_done at hstep
      | 2, _ => ms_done at hstep
      | 3, _ => ms_done at hstep
      | 4, _ => ms_done at hstep
      | r' + 5, _ => ms_done at hstep
    | cons d_inner R'' =>
      have hr := (AllGe1_cons.mp hR).1
      have hr2 : r ≥ 2 := by
        rcases Nat.lt_or_ge 2 (r + 1) with h | h
        · omega
        · -- r ≤ 1 ∧ r ≥ 1 ⟹ r = 1
          have h1 : r = 1 := by omega
          subst h1
          have hd := (AllGe1_cons.mp (AllGe1_cons.mp hR).2).1
          obtain ⟨d_inner', rfl⟩ : ∃ d', d_inner = d' + 1 := ⟨d_inner - 1, by omega⟩
          exact absurd rfl (hNH d_inner' R'')
      match r, hr2 with
      | 2, _ => ms_done at hstep
      | r' + 3, _ => ms_done at hstep

/-- **Single-R structural exclusion**: no `IntraEra` config has shape
    `M([], 3, [d])` for any d. Proof by induction on the IntraEra
    derivation:
    - **era_start**: era-starts have `L ≠ []`, contradicting `L = []`.
    - **step_within**: `macroStep_no_M_empty_3_single` rules out producing
      this shape from any predecessor with `MacroInvariant`. -/
theorem IntraEra.not_M_empty_3_single
    {cfg : MacroConfig} (h : IntraEra cfg) {d : Nat} :
    cfg ≠ .M [] 3 [d] := by
  induction h with
  | era_start e =>
    intro hcfg
    rw [EraStartConfig.toMacro, MacroConfig.M.injEq] at hcfg
    exact e.L_ne_nil hcfg.1
  | step_within h_prev hstep _ _ =>
    intro hcfg
    exact macroStep_no_M_empty_3_single h_prev.macroInvariant (hcfg ▸ hstep)

/-- IntraEraOf delegate of the singleton-R structural exclusion. -/
theorem IntraEraOf.not_M_empty_3_single {e : EraStartConfig}
    {cfg : MacroConfig} (h : IntraEraOf e cfg) {d : Nat} :
    cfg ≠ .M [] 3 [d] :=
  h.toIntraEra.not_M_empty_3_single

-- ============================================================
-- Stage D status (2026-05-06): partial — IntraEraOf framework only
-- ============================================================
-- The full Stage D claim from `plan-era-graded-not_R1.md` does NOT hold
-- as stated:
--
--   "∀ IntraEraOf e cfg with cfg = M([], 3, d::R'), e.toMacro = M([1], 5, [1])."
--
-- Counterexamples:
--   1. e = M([1, 2], 5, [1]) (Φ=9, |L|=2):
--      sweep → M([2, 2], 3, [2]) → sweep_and_shift → M([2], 3, [1, 3])
--      → sweep_and_shift → M([], 3, [1, 2, 3]).
--   2. e = M([1], 13, [1]) (Φ=15, singleton L) — sweeps oscillate between
--      |L|=0 and |L|=1 via sweep_left_empty:
--      5 sweeps → M([6], 3, [6]) → sweep_and_shift → M([], 7, [1, 7])
--      → sweep_left_empty → M([1], 5, [2, 7]) → sweep → M([2], 3, [3, 7])
--      → sweep_and_shift → M([], 3, [1, 4, 7]).
--
-- Orbit-reachability would constrain (1) (Φ=9 < depth-1 minimum 10), but
-- (2)'s Φ=15 may correspond to a depth-2 era-start. Whether such era-starts
-- are *actually* orbit-reachable depends on the orbit dynamics (era_and_*,
-- zero_two_*, zero_bounce_* recurrences from init); empirically (era-sim,
-- 63 K era boundaries) no R1-trigger has been observed, but proving this
-- formally requires a tighter characterization than the plan provides.
--
-- The IntraEraOf framework above is useful infrastructure for any future
-- approach (era-graded or other). What is provable easily:
--   • singleton-R: `IntraEraOf.not_M_empty_3_single` (delegate to
--     IntraEra-version). Excludes R = [d] singleton case directly.
--   • multi-R: open. Requires either (a) characterizing orbit-reachable
--     era-starts more tightly, or (b) a fundamentally different invariant
--     (e.g., a stronger Φ-like quantity that distinguishes R = [1, 3]
--     from other length-2 R outputs at the era-end).
--
-- Recommendation: see plan-era-graded-not_R1.md for revised path forward.

-- ============================================================
-- Lifting toward `OrbitReachable.not_R1` (partial — Approach 2)
-- ============================================================
-- The lifting theorem `OrbitReachable cfg → cfg ≠ M([], 3, R)` is the
-- ultimate goal of Strategy B. Proof by induction on `OrbitReachable`:
--
-- - **init**: `M([1], 4, [1]) ≠ M([], 3, R)` (trivially: L = [1] ≠ []).
-- - **step_macro**: macroStep producers of `M([], 3, R)` analyzed via
--   `macroStep_no_M_empty_3_single` (this file, single-R case) and
--   `macroStep_M_empty_3_predecessor` (`phase2.lean` Layer 0, multi-R
--   case via cascade).
-- - **step_run**: ⚠️ This is where the lifting hits its structural
--   obstacle. The constructor `OrbitReachable.step_run` takes an
--   arbitrary witness `run sweeper cfg.toConfig k = cfg'.toConfig` for
--   any `k > 0`, subject only to `MacroInvariant cfg'`. The constructor
--   does **not** track which macro rule (sweep, era_and_sweep,
--   multi_bounce_*, etc.) the run corresponds to.
--
--   In *actual* orbit construction (via `orbit_progress`), step_run is
--   invoked with a witness from `macro_progress`'s case dispatch — and
--   for each such case, the output cfg' has a specific shape never
--   equal to `M([], 3, [d])` (single-R case proved here; multi-R case
--   is the cascade of `phase2.lean`).
--
--   But the inductive predicate is more permissive: it allows ANY raw
--   TM run reaching ANY MacroInvariant config. To close the lift, one
--   would need either (a) a stronger invariant on `OrbitReachable`
--   that's preserved by arbitrary raw TM runs, or (b) a re-formulation
--   of `OrbitReachable` that explicitly tracks the macro-rule witness
--   per step. Both are out of scope for this round.

/-- Init case: the orbit's initial config differs from the R1 single-R
    shape. -/
theorem init_ne_M_empty_3_single {d : Nat} :
    (.M [1] 4 [1] : MacroConfig) ≠ .M [] 3 [d] := by
  intro h
  injection h with hL _
  exact List.cons_ne_nil _ _ hL

/-- Lifting toward closing R1: no `OrbitReachable` config has shape
    `M([], 3, R)` for any `R`. The strengthened predicate (universal in R)
    makes the `step_R1` case close via the inductive hypothesis on its
    predecessor (which is itself the R1 shape).

    Most constructor cases close structurally via output shape (non-empty
    L, c ≠ 3, or kind = M0). The `step_R3` case closes via the
    `h_safe` precondition baked into the constructor (discharged by
    `thm_reach_multi_bounce_last_2_long_safe`, which uses
    `shift_to_macro_prog_excludes_R1`).

    One case retains `sorry`:
    - `step_macro` multi-R case: requires cascade analysis (sweep_and_shift
      can produce `M([], 3, [1, ...])` from `M([2], 3, _)`; cascade tracked
      in `phase2.lean`). -/
theorem OrbitReachable.not_M_empty_3
    {cfg : MacroConfig} (h : OrbitReachable cfg) :
    ∀ R, cfg ≠ .M [] 3 R := by
  induction h with
  | init =>
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_macro h_prev h_step _ =>
    intro R hcfg
    -- macroStep would have to produce M([], 3, R). For R = [d] single,
    -- macroStep_no_M_empty_3_single closes. For R length ≥ 2, the
    -- producer is sweep_and_shift on M([2], 3, _), requiring cascade.
    have hsound := macroStep_sound _ _ _ h_step h_prev.macroInvariant
    cases R with
    | nil =>
      -- M([], 3, []) violates MacroInvariant (R ≠ [] required for M)
      rw [hcfg] at hsound
      exact hsound.2.1.2.2.2 rfl
    | cons d R' =>
      cases R' with
      | nil =>
        exact macroStep_no_M_empty_3_single h_prev.macroInvariant (hcfg ▸ h_step)
      | cons _ _ =>
        -- Multi-R case: cascade through M([2], 3, _) predecessors.
        sorry
  | step_multi_bounce_general _ _ =>
    -- output: M(R_mid.reverse ++ (r' + 1) :: (a + 4) :: L', last'' + 2, [1])
    -- L_out has ≥ 2 cons-elements, never []
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    obtain ⟨hL, _, _⟩ := hcfg
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) hL
  | step_multi_bounce_general_to_zero _ _ =>
    -- output: M0 (kind ≠ M)
    intro R hcfg; exact MacroConfig.noConfusion hcfg
  | step_multi_bounce_2_and_shift h_prev _ =>
    -- output: M((a + 4) :: L', r + 2, [1, 1]); L non-empty
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_multi_bounce_2_double_shift h_prev _ =>
    -- output: M(L', a + 4, [1, 1, 1]); c = a + 4 ≥ 5 ≠ 3 (a ≥ 1 from inv)
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    have ha : _ ≥ 1 := (AllGe1_cons.mp h_prev.macroInvariant.1).1
    omega
  | step_multi_bounce_3run_last_2 _ _ =>
    -- output: M((r' + 1) :: (a + 4) :: L', e + 2, [1, 1]); L non-empty
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_multi_bounce_last_2_general _ _ =>
    -- output: M(middle_init.reverse ++ (r' + 1) :: (a + 4) :: L', m_last + 2, [1, 1])
    -- L has cons part, never []
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) hcfg.1
  | step_R2_zero h_prev _ =>
    -- output: M(L', a + 4, [1, 1, 1, 1]); c = a + 4 ≥ 5 (a ≥ 1)
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    have ha : _ ≥ 1 := (AllGe1_cons.mp h_prev.macroInvariant.1).1
    omega
  | step_R2_succ _ _ =>
    -- output: M((a + 4) :: L', r + 2, [1, 1, 1]); L non-empty
    intro R hcfg
    rw [MacroConfig.M.injEq] at hcfg
    exact List.cons_ne_nil _ _ hcfg.1
  | step_R3 _ _ _ _ h_safe _ _ =>
    -- h_safe is the safety property baked into step_R3: cfg' ≠ M([], 3, R)
    -- for any R. Discharged in `orbit_progress` via
    -- `thm_reach_multi_bounce_last_2_long_safe` /
    -- `shift_to_macro_prog_excludes_R1`.
    exact h_safe
  | @step_R1 d_pre R'_pre _ _ _ _ _ _ ih =>
    -- IH says predecessor (M([], 3, d_pre :: R'_pre)) ≠ M([], 3, R) for any R.
    -- Specifically, instantiating R = d_pre :: R'_pre: contradiction.
    exact (ih (d_pre :: R'_pre) rfl).elim

-- ============================================================
-- shift_to_macro_prog structural analysis (moved to forward_dynamics.lean)
-- ============================================================
-- `shift_to_macro_prog_strong` and `shift_to_macro_prog_excludes_R1` are
-- now in `forward_dynamics.lean` (so `progress.lean`/`orbit_progress` can
-- use them when constructing `step_R3` witnesses with the safety
-- precondition).

end Sweeper
