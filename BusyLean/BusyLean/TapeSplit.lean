/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.TapeHelpers
import BusyLean.Attr

/-! # BusyLean: Tape Splitting Library

A controlled simp set `tape_split` that goes the **opposite** direction of
`tape_norm`: instead of merging adjacent `ones`/`zeros` runs, it *splits* a
merged `ones (n + k)` into `ones n ++ ones k`. This is used by `es`'s Stage 3
fallback in `esTryShift` to bridge the gap between merged-atom goals
(`ones (4 + 2*a)`) and split-atom shift rules (`ones 2 ++ L`).

**Important:** never use `tape_norm` and `tape_split` together — they go in
opposite directions and would loop. The `es` tactic only invokes `tape_split`
inside the Stage 3 fallback path, after Stage 0 and Stage 1 have failed.

### Splits provided

For each common shift-rule prefix size `n` (currently `2` and `4`), we
provide rules that split `ones (n + k)` into `ones n ++ ones k`. Both
positional variants (`n + k` and `k + n`) are provided so simp can fire
regardless of which side has the literal.
-/

namespace BusyLean

/-! ### `ones` splits

The split rules are stated with an explicit **left context** `L` to keep the
result LEFT-associated, matching how `++` parses in shift rules. Without
context the split would introduce right-association (`L ++ (ones n ++ rest)`),
which `isDefEq` cannot reconcile against the shift's `(L ++ ones n) ++ rest`.

`ones_4_peel_2_in` splits `L ++ ones (4 + k)` into `(L ++ ones 2) ++ ones (2 + k)`,
matching shift sources of the form `... ++ ones 2 ++ rest`.
-/

@[tape_split] theorem ones_4_peel_2_in (L : List Sym) (k : Nat) :
    L ++ ones (4 + k) = (L ++ ones 2) ++ ones (2 + k) := by
  rw [show 4 + k = 2 + (2 + k) from by omega, ← ones_append, ← List.append_assoc]

@[tape_split] theorem ones_6_peel_2_in (L : List Sym) (k : Nat) :
    L ++ ones (6 + k) = (L ++ ones 2) ++ ones (4 + k) := by
  rw [show 6 + k = 2 + (4 + k) from by omega, ← ones_append, ← List.append_assoc]

@[tape_split] theorem ones_6_peel_4_in (L : List Sym) (k : Nat) :
    L ++ ones (6 + k) = (L ++ ones 4) ++ ones (2 + k) := by
  rw [show 6 + k = 4 + (2 + k) from by omega, ← ones_append, ← List.append_assoc]

end BusyLean
