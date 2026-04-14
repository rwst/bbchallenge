/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.TapeHelpers
import BusyLean.Attr

/-! # BusyLean: Tape Normalization Library

A controlled simp set `tape_norm` for canonicalizing tape expressions during
the `es` tactic. The set prefers the *folded* form (`ones k`, `zebra k`, …)
over the raw cons form, so that shift-rule sources with metavariable indices
can be unified structurally.

See `BusyLean/PLAN.md` Phase 2.

### Usage

```
simp only [tape_norm]        -- normalize tape expressions in the goal
```

### Adding machine-specific atoms

Any file defining its own tape atoms (e.g. `rev_zebra`) can extend this set by
tagging its fold lemmas `@[tape_norm]`:

```
@[tape_norm] theorem rev_zebra_fold_cons_app (k : Nat) (R : List Sym) :
    true :: false :: (rev_zebra k ++ R) = rev_zebra (k + 1) ++ R := rfl
```
-/

namespace BusyLean

/-! ### ones / zeros folding

The folds go **cons → atom**, opposite of the `@[simp]` lemmas `ones_succ`,
`zeros_succ`. Using `simp only [tape_norm]` gives us the folding direction
without triggering default unfolds. -/

@[tape_norm] theorem ones_fold_cons (k : Nat) :
    true :: ones k = ones (k + 1) := rfl

@[tape_norm] theorem zeros_fold_cons (k : Nat) :
    false :: zeros k = zeros (k + 1) := rfl

@[tape_norm] theorem ones_fold_cons_app (k : Nat) (R : List Sym) :
    true :: (ones k ++ R) = ones (k + 1) ++ R := by
  show true :: ones k ++ R = ones (k + 1) ++ R
  rfl

@[tape_norm] theorem zeros_fold_cons_app (k : Nat) (R : List Sym) :
    false :: (zeros k ++ R) = zeros (k + 1) ++ R := by
  show false :: zeros k ++ R = zeros (k + 1) ++ R
  rfl

/-! ### zebra folding -/

@[tape_norm] theorem zebra_fold_cons (k : Nat) :
    false :: true :: zebra k = zebra (k + 1) := rfl

@[tape_norm] theorem zebra_fold_cons_app (k : Nat) (R : List Sym) :
    false :: true :: (zebra k ++ R) = zebra (k + 1) ++ R := by
  show false :: true :: zebra k ++ R = zebra (k + 1) ++ R
  rfl

/-! ### Append/list simplification -/

attribute [tape_norm]
  List.append_nil
  List.nil_append
  List.append_assoc
  List.cons_append

/-! ### Concatenation of same-atom runs (split form kept by default)

We do **not** tag `ones_append` / `zeros_append` / `zebra_append` here because
they go in the merge direction `ones a ++ ones b = ones (a+b)`, which combined
with variable indices produces non-canonical forms. Instead we eagerly fold
leading cons cells onto existing atoms via the lemmas above. -/

/-! ### Arithmetic normalization on tape indices -/

attribute [tape_norm]
  Nat.add_zero
  Nat.zero_add
  Nat.mul_zero
  Nat.zero_mul
  Nat.mul_one
  Nat.one_mul
  Nat.mul_add
  Nat.add_mul

end BusyLean
