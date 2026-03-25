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
-- Test 5: Cryptid machine
-- ============================================================

def cryptid : TM 6 := tm! "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"

example : run cryptid (initConfig 6) 1 =
    { state := some stB, left := [true], head := false, right := [] } := by decide

-- ============================================================
-- Test 6: BB(2) champion halts in 6 steps
-- ============================================================

def bb2 : TM 2 := tm! "1RB1LB_1LA---"

example : run bb2 (initConfig 2) 6 =
    ⟨none, [true], true, [true, true]⟩ := by tm_chain
