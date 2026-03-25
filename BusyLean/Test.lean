import BusyLean

open BusyLean

def antihydra : TM 6 := tm! "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

-- ============================================================
-- Test 1: decide for small concrete runs
-- ============================================================

example : run antihydra (initConfig 6) 1 =
    { state := some stB, left := [true], head := false, right := [] } := by decide

-- ============================================================
-- Test 2: tm_follow for manual chaining
-- ============================================================

theorem init_10 : run antihydra (initConfig 6) 10 =
    ⟨some stE, [true, true, true], true, [false]⟩ := by decide

theorem step_20 : run antihydra ⟨some stE, [true, true, true], true, [false]⟩ 10 =
    ⟨some stB, [true], true, [false, true, true, true, false]⟩ := by decide

theorem init_20 : run antihydra (initConfig 6) 20 =
    run antihydra (⟨some stE, [true, true, true], true, [false]⟩) 10 := by
  tm_follow init_10

-- ============================================================
-- Test 3: tm_chain for automatic chaining
-- ============================================================

-- 58 steps in one shot — automatically splits into 10-step chunks
example : run antihydra (initConfig 6) 58 =
    ⟨some stE, [true, true, true, true, true, true, true, true, false, true, true],
      false, []⟩ := by tm_chain

-- Custom chunk size
example : run antihydra (initConfig 6) 58 =
    ⟨some stE, [true, true, true, true, true, true, true, true, false, true, true],
      false, []⟩ := by tm_chain 15

-- ============================================================
-- Test 4: symbolic step with simp
-- ============================================================

example (L R : List Sym) :
    step antihydra { state := some stA, left := L, head := true, right := R } =
    { state := some stA, left := true :: L, head := listHead R false,
      right := listTail R } := by
  simp [step, antihydra]

-- ============================================================
-- Test 5: shift rule by induction
-- ============================================================

-- Transition lemma (keeps antihydra folded in subsequent goals)
theorem step_A_true (L R : List Sym) :
    step antihydra ⟨some stA, L, true, R⟩ =
    ⟨some stA, true :: L, listHead R false, listTail R⟩ := by
  simp [step, antihydra]

-- State A scans right through k ones
theorem A_shift (k : Nat) : ∀ (L R : List Sym),
    run antihydra ⟨some stA, L, true, ones k ++ R⟩ (k + 1) =
    ⟨some stA, ones (k + 1) ++ L, listHead R false, listTail R⟩ := by
  induction k with
  | zero =>
    intro L R; simp only [ones_zero, List.nil_append]; exact step_A_true L R
  | succ n ih =>
    intro L R
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl, run_succ,
        ones_succ, List.cons_append, step_A_true, listHead_cons, listTail_cons]
    rw [ih (true :: L) R]
    simp [ones_succ]

-- ============================================================
-- Test 6: non-halting via progress invariant
-- ============================================================

-- Simple 1-state machine that loops forever (no halt transition)
def loop1 : TM 1 := tm! "1RA1RA"

theorem loop1_nonhalt : ∀ m, (run loop1 (initConfig 1) m).state ≠ none := by
  apply nonhalt_of_progress loop1 (fun c => c.state ≠ none)
  · intro c hc
    refine ⟨1, by omega, ?_, ?_⟩
    all_goals {
      simp only [run]
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
      have : q = ⟨0, by omega⟩ := by ext; omega
      subst this; simp only [step, hq, loop1]
      cases c.head <;> simp
    }
  · simp [initConfig]

-- ============================================================
-- Test 7: Cryptid machine + BB(2) champion
-- ============================================================

def cryptid : TM 6 := tm! "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"

example : run cryptid (initConfig 6) 1 =
    { state := some stB, left := [true], head := false, right := [] } := by decide

def bb2 : TM 2 := tm! "1RB1LB_1LA---"

example : run bb2 (initConfig 2) 6 =
    ⟨none, [true], true, [true, true]⟩ := by tm_chain
