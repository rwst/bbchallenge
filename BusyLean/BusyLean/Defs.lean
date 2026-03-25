/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# BusyLean: Core Turing Machine Definitions

Lightweight infrastructure for Busy Beaver proofs in Lean 4.
Binary alphabet, zipper tape, parametric over state count.
-/

namespace BusyLean

/-- Binary tape symbol: `false` = 0 (blank), `true` = 1. Matches bbchallenge convention. -/
abbrev Sym := Bool

/-- Tape head movement direction. -/
inductive Dir where
  | L
  | R
  deriving DecidableEq, Repr, BEq

/-- A Turing machine with `n` non-halt states over binary alphabet.
    Transition returns `none` for halt. -/
structure TM (n : Nat) where
  /-- Transition function: state × symbol → Option (new_state, write_symbol, direction).
      `none` means halt. -/
  tr : Fin n → Sym → Option (Fin n × Sym × Dir)
  deriving Inhabited

instance {n : Nat} : Repr (TM n) where
  reprPrec tm _ :=
    let entries := (List.finRange n).flatMap fun q =>
      [false, true].map fun s =>
        let res := tm.tr q s
        s!"{repr q},{repr s} => {repr res}"
    "TM{" ++ ", ".intercalate entries ++ "}"

/-- Configuration of a TM: zipper tape with state.
    `state = none` means halted. -/
structure Config (n : Nat) where
  /-- Current state, or `none` if halted -/
  state : Option (Fin n)
  /-- Tape cells to the left of head (reversed: first element is immediately left) -/
  left  : List Sym
  /-- Symbol currently under the head -/
  head  : Sym
  /-- Tape cells to the right of head (first element is immediately right) -/
  right : List Sym
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Whether a configuration is halted. -/
def Config.halted {n : Nat} (c : Config n) : Prop := c.state = none

instance {n : Nat} (c : Config n) : Decidable c.halted :=
  inferInstanceAs (Decidable (c.state = none))

/-- Head of a list with default value. Defined directly for optimal `simp` behavior. -/
@[simp]
def listHead {α : Type} (l : List α) (default : α) : α :=
  match l with
  | [] => default
  | a :: _ => a

/-- Tail of a list, returning `[]` for empty. Defined directly for optimal `simp` behavior. -/
@[simp]
def listTail {α : Type} (l : List α) : List α :=
  match l with
  | [] => []
  | _ :: as => as

/-- Execute one step of the Turing machine. Identity on halted configurations. -/
@[simp]
def step {n : Nat} (tm : TM n) (c : Config n) : Config n :=
  match c.state with
  | none => c
  | some q =>
    match tm.tr q c.head with
    | none => { state := none, left := c.left, head := c.head, right := c.right }
    | some (q', w, d) =>
      match d with
      | Dir.R =>
        { state := some q',
          left := w :: c.left,
          head := listHead c.right false,
          right := listTail c.right }
      | Dir.L =>
        { state := some q',
          left := listTail c.left,
          head := listHead c.left false,
          right := w :: c.right }

/-- Run the machine for `k` steps. -/
def run {n : Nat} (tm : TM n) (c : Config n) : Nat → Config n
  | 0 => c
  | k + 1 => run tm (step tm c) k

/-- Initial configuration: state 0, blank tape. -/
def initConfig (n : Nat) (h : 0 < n := by omega) : Config n :=
  { state := some ⟨0, h⟩,
    left := [],
    head := false,
    right := [] }

end BusyLean
