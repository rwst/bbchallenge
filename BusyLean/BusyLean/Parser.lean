/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import Lean.Elab.Term

/-!
# BusyLean: TM String Parser

Parse Turing machines from the standard bbchallenge string format:

    "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

## `tm!` macro

`tm! "1RB1RA_..."` generates a `TM n` at elaboration time with a kernel-reducible
transition function (a direct `match` on `q.val` and `s`), enabling `decide` on
concrete configurations.
-/

namespace BusyLean

/-- Raw string parser. Returns (numStates, transitions) where each transition is
    (state_idx, is_sym_1, result). -/
private def parseTransitions (s : String) :
    Except String (Nat × Array (Nat × Bool × Option (Nat × Bool × Bool))) := do
  let mut result : Array (Nat × Bool × Option (Nat × Bool × Bool)) := #[]
  let mut stateIdx := 0
  let mut cs := s.toList
  while !cs.isEmpty do
    let (t0, rest0) ← parseOne cs stateIdx false
    result := result.push t0
    let (t1, rest1) ← parseOne rest0 stateIdx true
    result := result.push t1
    cs := match rest1 with
      | '_' :: rest => rest
      | other => other
    stateIdx := stateIdx + 1
  return (stateIdx, result)
where
  parseOne (cs : List Char) (stIdx : Nat) (sym : Bool) :
      Except String ((Nat × Bool × Option (Nat × Bool × Bool)) × List Char) :=
    match cs with
    | '-' :: '-' :: '-' :: rest =>
      .ok ((stIdx, sym, none), rest)
    | c1 :: c2 :: c3 :: rest => do
      let writeSym ← match c1 with
        | '0' => .ok false | '1' => .ok true
        | _ => .error s!"Invalid symbol char: {c1}"
      let dirRight ← match c2 with
        | 'L' => .ok false | 'R' => .ok true
        | _ => .error s!"Invalid direction char: {c2}"
      let targetState ← if c3.toNat >= 'A'.toNat && c3.toNat <= 'Z'.toNat
        then .ok (c3.toNat - 'A'.toNat)
        else .error s!"Invalid state char: {c3}"
      .ok ((stIdx, sym, some (targetState, writeSym, dirRight)), rest)
    | _ => .error "Unexpected end of string"

/-- Generate a string containing a Lean `def` for the TM, with a direct match.
    This is used by the `tm!` macro to produce kernel-reducible code. -/
private def generateTMSource (tmStr : String) : Except String (Nat × String) := do
  let (numStates, transitions) ← parseTransitions tmStr
  let mut arms := ""
  for (stIdx, sym, result) in transitions.toList do
    let symStr := if sym then "true" else "false"
    let rhsStr ← match result with
      | none => pure "none"
      | some (tgt, wr, dirR) =>
        let wrStr := if wr then "true" else "false"
        let dirStr := if dirR then "Dir.R" else "Dir.L"
        pure s!"some (⟨{tgt}, by omega⟩, {wrStr}, {dirStr})"
    arms := arms ++ s!"  | {stIdx}, {symStr} => {rhsStr}\n"
  arms := arms ++ "  | _, _ => none"
  let src := s!"fun q s => match q.val, s with\n{arms}"
  return (numStates, src)

open Lean Elab Term in
/-- `tm! "1RB1RA_0LC1LE_..."` parses a bbchallenge TM string at elaboration time
    and generates a `TM n` with a direct match-based transition function.

    The generated transition function matches directly on `q.val` and `s`,
    ensuring kernel reducibility so `decide` works on concrete configurations. -/
elab "tm! " s:str : term <= expectedType? => do
  let str := s.getString
  let (numStates, src) ← match generateTMSource str with
    | .ok r => pure r
    | .error msg => throwError "tm! parse error: {msg}"
  -- Parse the generated source as Lean syntax
  let fullSrc := s!"\{ tr := {src} : TM {numStates} }"
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term fullSrc with
    | .ok stx => pure stx
    | .error msg => throwError "tm! internal parse error: {msg}"
  elabTerm (Unhygienic.run `(term| $(⟨stx⟩))) expectedType?

-- ============================================================
-- Runtime parser (for #eval, not kernel-reducible)
-- ============================================================

def parseSym (c : Char) : Option Sym :=
  if c == '0' then some false
  else if c == '1' then some true
  else none

def parseDir (c : Char) : Option Dir :=
  if c == 'L' then some Dir.L
  else if c == 'R' then some Dir.R
  else none

def parseState (n : Nat) (c : Char) : Option (Fin n) :=
  let idx := c.toNat - 'A'.toNat
  if h : idx < n then some ⟨idx, h⟩ else none

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

def parseStatePair (n : Nat) (chars : List Char) :
    Option ((Option (Fin n × Sym × Dir)) × (Option (Fin n × Sym × Dir)) × List Char) := do
  let (t0, rest1) ← parseTrans n chars
  let (t1, rest2) ← parseTrans n rest1
  let rest3 := match rest2 with
    | '_' :: rest => rest
    | other => other
  some (t0, t1, rest3)

def parseAllStates (n : Nat) : Nat → List Char →
    Option (List (Option (Fin n × Sym × Dir) × Option (Fin n × Sym × Dir))) :=
  fun remaining chars =>
    match remaining with
    | 0 => some []
    | k + 1 => do
      let (t0, t1, rest) ← parseStatePair n chars
      let tail ← parseAllStates n k rest
      some ((t0, t1) :: tail)

def buildTR (n : Nat) (pairs : List (Option (Fin n × Sym × Dir) × Option (Fin n × Sym × Dir)))
    (q : Fin n) (s : Sym) : Option (Fin n × Sym × Dir) :=
  match pairs[q.val]? with
  | none => none
  | some (t0, t1) => if s then t1 else t0

def parseTM (s : String) (n : Nat) : Option (TM n) := do
  let chars := s.toList
  let pairs ← parseAllStates n n chars
  some { tr := buildTR n pairs }

def parseTM! (s : String) (n : Nat) : TM n :=
  match parseTM s n with
  | some tm => tm
  | none => panic! s!"Failed to parse TM string: {s}"

end BusyLean
