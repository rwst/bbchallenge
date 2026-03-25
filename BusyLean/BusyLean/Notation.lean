/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.TapeHelpers

/-!
# BusyLean: Tape and Configuration Notation

Concise notation for BB proof tape patterns, inspired by BusyCoq.

## Notation summary

### List repetition
- `xs ×× n` — repeat list `xs` `n` times: `[true, false] ×× 3` = `[1,0,1,0,1,0]`
- `ones n` / `zeros n` — `n` copies of 1 / 0 (from TapeHelpers)

### Configuration builder
- `⟪ q | left | head | right ⟫` — build a Config 6

### State names
- `stA` through `stF` for BB(6) states

## Examples

Antihydra's P_Config_Pad b m n p becomes:
```
⟪ stE | ones m ++ [false] ++ ones b | false | ones n ++ zeros p ⟫
```
vs the old verbose form:
```
{ state := some ⟨4, by decide⟩, head := false,
  left := repeatOne m ++ [false] ++ repeatOne b,
  right := repeatOne n ++ repeatFalse p }
```
-/

namespace BusyLean

/-! ### List repetition -/

/-- Repeat a list `n` times. -/
def listRepeat {α : Type} (xs : List α) : Nat → List α
  | 0 => []
  | n + 1 => xs ++ listRepeat xs n

/-- `xs ×× n` repeats list `xs` `n` times. -/
scoped infixl:70 " ×× " => listRepeat

@[simp] theorem listRepeat_zero {α : Type} (xs : List α) : xs ×× 0 = [] := rfl
@[simp] theorem listRepeat_succ {α : Type} (xs : List α) (n : Nat) :
    xs ×× (n + 1) = xs ++ xs ×× n := rfl

theorem listRepeat_add {α : Type} (xs : List α) (a b : Nat) :
    xs ×× (a + b) = xs ×× a ++ xs ×× b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    simp [h, ih, List.append_assoc]

/-- `[true] ×× n = ones n` -/
@[simp] theorem singleton_true_repeat (n : Nat) : [true] ×× n = ones n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- `[false] ×× n = zeros n` -/
@[simp] theorem singleton_false_repeat (n : Nat) : [false] ×× n = zeros n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-! ### State name helpers -/

-- Common state abbreviations for BB(6)
abbrev stA : Fin 6 := ⟨0, by omega⟩
abbrev stB : Fin 6 := ⟨1, by omega⟩
abbrev stC : Fin 6 := ⟨2, by omega⟩
abbrev stD : Fin 6 := ⟨3, by omega⟩
abbrev stE : Fin 6 := ⟨4, by omega⟩
abbrev stF : Fin 6 := ⟨5, by omega⟩

/-! ### Configuration builder -/

/-- Build a `Config n` from state, left tape (visual order), head, and right tape.
    The left tape is given leftmost-first and reversed internally to match
    the zipper representation. -/
@[inline]
def mkConfig (n : Nat) (q : Option (Fin n)) (left : List Sym) (hd : Sym)
    (right : List Sym) : Config n :=
  { state := q, left := left.reverse, head := hd, right := right }

/-- Notation: `⟪ q | left | head | right ⟫` builds a `Config 6`.
    Left tape is in visual order (leftmost symbol first).
    Use `none` for halt state, `some stX` for state X. -/
scoped notation "⟪" q " | " l " | " h " | " r " ⟫" =>
  mkConfig 6 q l h r

/-- Shorthand: `⟪ q | left | head | right ⟫` with a non-option state. -/
scoped notation "⟪! " q " | " l " | " h " | " r " ⟫" =>
  mkConfig 6 (some q) l h r

/-! ### Simp lemmas for mkConfig -/

@[simp] theorem mkConfig_state {n : Nat} (q : Option (Fin n)) (l : List Sym)
    (h : Sym) (r : List Sym) :
    (mkConfig n q l h r).state = q := rfl

@[simp] theorem mkConfig_head {n : Nat} (q : Option (Fin n)) (l : List Sym)
    (h : Sym) (r : List Sym) :
    (mkConfig n q l h r).head = h := rfl

@[simp] theorem mkConfig_right {n : Nat} (q : Option (Fin n)) (l : List Sym)
    (h : Sym) (r : List Sym) :
    (mkConfig n q l h r).right = r := rfl

@[simp] theorem mkConfig_left {n : Nat} (q : Option (Fin n)) (l : List Sym)
    (h : Sym) (r : List Sym) :
    (mkConfig n q l h r).left = l.reverse := rfl

end BusyLean
