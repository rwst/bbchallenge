/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs

/-!
# BusyLean: Tape Helper Definitions and Lemmas

Common tape manipulation utilities for BB proofs:
repeated symbols, counting, and simp lemmas.
-/

namespace BusyLean

/-- `k` copies of symbol `s`. -/
abbrev repeatSym (s : Sym) (k : Nat) : List Sym := List.replicate k s

/-- `k` copies of `true` (1). -/
abbrev ones (k : Nat) : List Sym := repeatSym true k

/-- `k` copies of `false` (0/blank). -/
abbrev zeros (k : Nat) : List Sym := repeatSym false k

/-- Count leading `true` symbols in a list. -/
def countOnes : List Sym → Nat
  | [] => 0
  | true :: xs => countOnes xs + 1
  | false :: _ => 0

/-- Count leading `false` symbols in a list. -/
def countZeros : List Sym → Nat
  | [] => 0
  | false :: xs => countZeros xs + 1
  | true :: _ => 0

-- Simp lemmas for ones/zeros

@[simp] theorem ones_zero : ones 0 = [] := rfl
@[simp] theorem ones_succ (k : Nat) : ones (k + 1) = true :: ones k := rfl
@[simp] theorem zeros_zero : zeros 0 = [] := rfl
@[simp] theorem zeros_succ (k : Nat) : zeros (k + 1) = false :: zeros k := rfl

@[simp] theorem countOnes_nil : countOnes [] = 0 := rfl
@[simp] theorem countOnes_true (xs : List Sym) :
    countOnes (true :: xs) = countOnes xs + 1 := rfl
@[simp] theorem countOnes_false (xs : List Sym) :
    countOnes (false :: xs) = 0 := rfl
@[simp] theorem countOnes_ones (k : Nat) : countOnes (ones k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

theorem replicate_append {α : Type} (a b : Nat) (x : α) :
    List.replicate a x ++ List.replicate b x = List.replicate (a + b) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    simp [List.replicate, List.cons_append, ih, h]

@[simp] theorem ones_append (a b : Nat) :
    ones a ++ ones b = ones (a + b) :=
  replicate_append a b true

@[simp] theorem zeros_append (a b : Nat) :
    zeros a ++ zeros b = zeros (a + b) :=
  replicate_append a b false

-- listHead / listTail lemmas for common patterns

@[simp] theorem listHead_cons {α : Type} (a : α) (l : List α) (d : α) :
    listHead (a :: l) d = a := rfl

@[simp] theorem listHead_nil {α : Type} (d : α) :
    listHead ([] : List α) d = d := rfl

@[simp] theorem listTail_cons {α : Type} (a : α) (l : List α) :
    listTail (a :: l) = l := rfl

@[simp] theorem listTail_nil {α : Type} :
    listTail ([] : List α) = [] := rfl

end BusyLean
