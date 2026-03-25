import BusyLean

open BusyLean

def antihydra : TM 6 := tm! "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

-- ============================================================
-- Test 1: decide for small concrete runs
-- ============================================================

example : run antihydra (initConfig 6) 1 =
    { state := some stB, left := [true], head := false, right := [] } := by decide

-- ============================================================
-- Test 2: tm_follow chaining to reach 58 steps
-- ============================================================

-- 10 steps
theorem init_10 : run antihydra (initConfig 6) 10 =
    ⟨some stE, [true, true, true], true, [false]⟩ := by decide

-- 20 = 10 + 10
theorem step_20 : run antihydra ⟨some stE, [true, true, true], true, [false]⟩ 10 =
    ⟨some stB, [true], true, [false, true, true, true, false]⟩ := by decide

-- 30 = 20 + 10
theorem step_30 :
    run antihydra ⟨some stB, [true], true, [false, true, true, true, false]⟩ 10 =
    ⟨some stB, [true, true, true, true, true, false, true], false, []⟩ := by decide

-- 40 = 30 + 10
theorem step_40 :
    run antihydra ⟨some stB, [true, true, true, true, true, false, true], false, []⟩ 10 =
    ⟨some stD, [], false, [true, false, false, true, true, true, true, true, true, false]⟩ := by
  decide

-- 48 = 40 + 8
theorem step_48 :
    run antihydra ⟨some stD, [], false,
      [true, false, false, true, true, true, true, true, true, false]⟩ 8 =
    ⟨some stA, [false, true, true], true,
      [false, true, true, true, true, true, true, false]⟩ := by decide

-- 58 = 48 + 10
theorem step_58 :
    run antihydra ⟨some stA, [false, true, true], true,
      [false, true, true, true, true, true, true, false]⟩ 10 =
    ⟨some stE, [true, true, true, true, true, true, true, true, false, true, true],
      false, []⟩ := by decide

-- Chain them all: 58 steps from init
theorem init_58 : run antihydra (initConfig 6) 58 =
    ⟨some stE, [true, true, true, true, true, true, true, true, false, true, true],
      false, []⟩ := by
  tm_follow init_10
  tm_follow step_20
  tm_follow step_30
  tm_follow step_40
  tm_follow step_48
  tm_follow step_58

-- ============================================================
-- Test 3: symbolic step with simp
-- ============================================================

-- State A reading true: move right, write true, stay in A
example (L R : List Sym) :
    step antihydra { state := some stA, left := L, head := true, right := R } =
    { state := some stA, left := true :: L, head := listHead R false,
      right := listTail R } := by
  simp [step, antihydra]

-- ============================================================
-- Test 4: Cryptid machine parses and runs
-- ============================================================

def cryptid : TM 6 := tm! "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC"

example : run cryptid (initConfig 6) 1 =
    { state := some stB, left := [true], head := false, right := [] } := by decide
