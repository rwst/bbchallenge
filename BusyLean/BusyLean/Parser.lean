/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs

/-!
# BusyLean: TM String Parser

Parse Turing machines from the standard bbchallenge string format:

    "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

States separated by `_`. Each state has two transitions (for symbol 0 then 1).
Each transition is 3 characters: `[01][LR][A-Z]` or `---` for halt.
-/

namespace BusyLean

/-- Parse a symbol character ('0' or '1'). -/
def parseSym (c : Char) : Option Sym :=
  if c == '0' then some false
  else if c == '1' then some true
  else none

/-- Parse a direction character ('L' or 'R'). -/
def parseDir (c : Char) : Option Dir :=
  if c == 'L' then some Dir.L
  else if c == 'R' then some Dir.R
  else none

/-- Parse a state character ('A' = 0, 'B' = 1, ...). Returns `Fin n` if in range. -/
def parseState (n : Nat) (c : Char) : Option (Fin n) :=
  let idx := c.toNat - 'A'.toNat
  if h : idx < n then some ⟨idx, h⟩ else none

/-- Parse a single 3-character transition from a char list.
    Returns the transition and remaining chars.
    `---` maps to halt (`none`). -/
def parseTrans (n : Nat) (chars : List Char) :
    Option (Option (Fin n × Sym × Dir) × List Char) :=
  match chars with
  | '-' :: '-' :: '-' :: rest => some (none, rest)
  | c1 :: c2 :: c3 :: rest => do
    let sym ← parseSym c1
    let dir ← parseDir c2
    let st ← parseState n c3
    some (some (st, sym, dir), rest)
  | _ => none

/-- Parse transitions for one state (two transitions + optional separator).
    Returns (transition_for_0, transition_for_1, remaining_chars). -/
def parseStatePair (n : Nat) (chars : List Char) :
    Option ((Option (Fin n × Sym × Dir)) × (Option (Fin n × Sym × Dir)) × List Char) := do
  let (t0, rest1) ← parseTrans n chars
  let (t1, rest2) ← parseTrans n rest1
  -- Skip optional underscore separator
  let rest3 := match rest2 with
    | '_' :: rest => rest
    | other => other
  some (t0, t1, rest3)

/-- Parse all state pairs from a char list. -/
def parseAllStates (n : Nat) : Nat → List Char →
    Option (List (Option (Fin n × Sym × Dir) × Option (Fin n × Sym × Dir))) :=
  fun remaining chars =>
    match remaining with
    | 0 => some []
    | k + 1 => do
      let (t0, t1, rest) ← parseStatePair n chars
      let tail ← parseAllStates n k rest
      some ((t0, t1) :: tail)

/-- Build a transition function from a list of (trans_for_0, trans_for_1) pairs. -/
def buildTR (n : Nat) (pairs : List (Option (Fin n × Sym × Dir) × Option (Fin n × Sym × Dir)))
    (q : Fin n) (s : Sym) : Option (Fin n × Sym × Dir) :=
  match pairs[q.val]? with
  | none => none
  | some (t0, t1) => if s then t1 else t0

/-- Parse a bbchallenge TM string into a `TM n`.
    The number of states `n` must be provided and must match the string. -/
def parseTM (s : String) (n : Nat) : Option (TM n) := do
  let chars := s.toList
  let pairs ← parseAllStates n n chars
  some { tr := buildTR n pairs }

/-- Parse a TM string, panicking on failure. For use with `Eval compute in`. -/
def parseTM! (s : String) (n : Nat) : TM n :=
  match parseTM s n with
  | some tm => tm
  | none => panic! s!"Failed to parse TM string: {s}"

end BusyLean
