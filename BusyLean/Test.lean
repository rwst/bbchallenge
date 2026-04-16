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

-- tm_follow with have-bound hypothesis (mdata bug fix, item 8)
-- Variant A: local have-bound hypothesis (originally failed with mdata bug)
theorem init_20a : run antihydra (initConfig 6) 20 =
    ⟨some stB, [true], true, [false, true, true, true, false]⟩ := by
  have h : run antihydra (initConfig 6) 10 =
      ⟨some stE, [true, true, true], true, [false]⟩ := by decide
  tm_follow h  -- auto-closes: remaining 10 steps are kernel-reducible

-- Variant B: direct theorem reference
theorem init_20b : run antihydra (initConfig 6) 20 =
    ⟨some stB, [true], true, [false, true, true, true, false]⟩ := by
  tm_follow init_10  -- auto-closes via rfl on remaining steps

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

-- ============================================================
-- Test 8: Trans instances for EvStep (item 10)
-- ============================================================

-- Abbreviations for 2-state TM
private abbrev st2A : Fin 2 := ⟨0, by omega⟩
private abbrev st2B : Fin 2 := ⟨1, by omega⟩

-- calc-style chaining of →* steps via Trans EvStep EvStep EvStep
example : (initConfig 2 : Config 2) -[bb2]->* ⟨none, [true], true, [true, true]⟩ :=
  calc (initConfig 2 : Config 2)
      _ -[bb2]->* ⟨some st2B, [], false, [true, true]⟩       := ⟨3, by decide⟩
      _ -[bb2]->* ⟨none, [true], true, [true, true]⟩         := ⟨3, by decide⟩

-- calc-style with mixed Multistep/EvStep via Trans Multistep EvStep EvStep
example : (initConfig 2 : Config 2) -[bb2]->* ⟨none, [true], true, [true, true]⟩ :=
  calc (initConfig 2 : Config 2)
      _ -[bb2]{3}-> ⟨some st2B, [], false, [true, true]⟩     := by decide
      _ -[bb2]->*   ⟨none, [true], true, [true, true]⟩       := ⟨3, by decide⟩

-- ============================================================
-- Test 9: zebra (item 14)
-- ============================================================

example : zebra 0 = [] := by simp
example : zebra 3 = [false, true, false, true, false, true] := by rfl
example : zebra 2 ++ zebra 1 = zebra 3 := by rw [zebra_append]
example : (zebra 4).length = 8 := by simp

-- ============================================================
-- Test 10: mkConfigFromTape (item 15)
-- ============================================================

-- Extracts head from the tape list
example : mkConfigFromTape 6 stC (ones 3) (false :: true :: [true]) =
    { state := some stC, left := ones 3, head := false, right := [true, true] } := by rfl

-- Empty tape → head = false (blank)
example : mkConfigFromTape 6 stA [] [] =
    { state := some stA, left := [], head := false, right := [] } := by rfl

-- Non-halted
example : ¬ (mkConfigFromTape 6 stC (ones 3) (zebra 2 ++ [true])).halted :=
  mkConfigFromTape_halted stC _ _

-- ============================================================
-- Test 11: evstep_follow / evstep_finish (item 11)
-- ============================================================

-- evstep_follow with EvStep hypothesis
example : (initConfig 2 : Config 2) -[bb2]->* ⟨none, [true], true, [true, true]⟩ := by
  have h : (initConfig 2 : Config 2) -[bb2]->*
      ⟨some st2B, [], false, [true, true]⟩ := ⟨3, by decide⟩
  evstep_follow h
  exact ⟨3, by decide⟩

-- evstep_follow with run-equality hypothesis
example : (initConfig 2 : Config 2) -[bb2]->* ⟨none, [true], true, [true, true]⟩ := by
  have h : run bb2 (initConfig 2) 3 =
      ⟨some st2B, [], false, [true, true]⟩ := by decide
  evstep_follow h
  exact ⟨3, by decide⟩

-- evstep_finish closes trivial reflexivity
example : (⟨some stA, [], false, []⟩ : Config 6) -[antihydra]->*
    ⟨some stA, [], false, []⟩ := by
  evstep_finish

-- evstep_finish with arithmetic normalization (omega closes fields)
example (n : Nat) :
    (⟨some stA, ones (n + 3), false, ones (2 * n + 1)⟩ : Config 6) -[antihydra]->*
    ⟨some stA, ones (3 + n), false, ones (1 + 2 * n)⟩ := by
  evstep_finish
