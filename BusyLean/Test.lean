import BusyLean

open BusyLean

-- Parse the Antihydra machine from its bbchallenge string
def antihydra : TM 6 := parseTM! "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA" 6

-- Verify transitions match the hand-written table in Antihydra.lean
-- State A (0): false → (B, 1, R), true → (A, 1, R)
#eval antihydra.tr ⟨0, by omega⟩ false  -- should be some (1, true, R)
#eval antihydra.tr ⟨0, by omega⟩ true   -- should be some (0, true, R)
-- State B (1): false → (C, 0, L), true → (E, 1, L)
#eval antihydra.tr ⟨1, by omega⟩ false  -- should be some (2, false, L)
#eval antihydra.tr ⟨1, by omega⟩ true   -- should be some (4, true, L)
-- State F (5): false → halt, true → (A, 0, R)
#eval antihydra.tr ⟨5, by omega⟩ false  -- should be none (halt)
#eval antihydra.tr ⟨5, by omega⟩ true   -- should be some (0, false, R)

-- Run from initial config
def ic : Config 6 := initConfig 6

-- Check a few steps
#eval step antihydra ic
#eval run antihydra ic 10
#eval run antihydra ic 58

-- Parse the Cryptid machine too
def cryptid : TM 6 := parseTM! "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC" 6
#eval cryptid.tr ⟨0, by omega⟩ false  -- should be some (1, true, R)
#eval cryptid.tr ⟨0, by omega⟩ true   -- should be some (1, false, R)
