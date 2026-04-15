/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.TapeHelpers
import BusyLean.RunLemmas
import BusyLean.Multistep

/-! # BusyLean: Shift Rule Lifting

Generic machinery for lifting a 1-iteration TM computation to an n-iteration
version via induction. Ported from BusyCoq's `Individual62.v:227-264`
(`shift_rule_L` and `shift_rule_R`).

### The idea

BusyCoq's `shift_rule_L` takes a proof that a 1-cell/1-segment configuration
reaches a shifted configuration in finitely many steps:

```
∀ L R, {Q, x ++ L, d, R} -[tm]->* {Q, L, d, x' ++ R}
```

and produces the `n`-iteration version:

```
∀ L R n, {Q, (List.replicate n x).flatten ++ L, d, R} -[tm]->*
         {Q, L, d, (List.replicate n x').flatten ++ R}
```

This is the engine behind BusyCoq's one-line halting proofs — the user writes
a 1-segment lemma (often provable by `decide` or `rfl` for small concrete
segments) and the lifting does the inductive work.

### Names

We use `listPow xs n = (List.replicate n xs).flatten` (BusyCoq's `xs^^n`)
throughout. The key correspondence:
- `rev_zebra n = listPow [true, false] n`
- `zebra n = listPow [false, true] n`
- `ones n = listPow [true] n`
- `zeros n = listPow [false] n`

### Limitation

Unlike BusyCoq's `shift_rule_L`, this lemma assumes the state `Q` and head
symbol `d` are preserved EXACTLY across a 1-iteration. For TMs where the
state/head changes between iterations, a more complex formulation is needed.
-/

namespace BusyLean

variable {n : Nat} {tm : TM n}

/-- Repeat a list `xs` `k` times and flatten. Equivalent to BusyCoq's `xs^^k`. -/
def listPow (xs : List Sym) (k : Nat) : List Sym :=
  (List.replicate k xs).flatten

@[simp] theorem listPow_zero (xs : List Sym) : listPow xs 0 = [] := rfl

@[simp] theorem listPow_succ (xs : List Sym) (k : Nat) :
    listPow xs (k + 1) = xs ++ listPow xs k := by
  simp [listPow, List.replicate]

/-- Helper: `listPow xs (k+1) = listPow xs k ++ xs` (the other direction of `listPow_succ`). -/
private theorem listPow_succ_right (xs : List Sym) (k : Nat) :
    listPow xs (k + 1) = listPow xs k ++ xs := by
  induction k with
  | zero => simp [listPow_zero, listPow_succ]
  | succ k ih =>
    calc listPow xs (k + 1 + 1)
        = xs ++ listPow xs (k + 1) := by rw [listPow_succ]
      _ = xs ++ (listPow xs k ++ xs) := by rw [ih]
      _ = (xs ++ listPow xs k) ++ xs := by rw [List.append_assoc]
      _ = listPow xs (k + 1) ++ xs := by rw [← listPow_succ]

/-- **Left shift rule lifting (BusyCoq `shift_rule_L`)**: if a 1-iteration of
    segment consumption on the left holds generically, the n-iteration holds
    for any `n` by induction. This is the engine that lets the user prove
    segment-iteration lemmas by proving a single "1-cell" base case.

    The 1-iteration premise says: from `{Q, x ++ L, d, R}` the machine reaches
    `{Q, L, d, x' ++ R}` (segment `x` on the left consumed, replaced by `x'`
    on the right, same state and head). The conclusion lifts this to iterating
    `n` copies of `x`. -/
theorem shift_rule_L_lift (tm : TM n) (q : Option (Fin n)) (d : Sym)
    (x x' : List Sym)
    (h1 : ∀ L R : List Sym,
      ({state := q, left := x ++ L, head := d, right := R} : Config n) -[tm]->*
      {state := q, left := L, head := d, right := x' ++ R}) :
    ∀ (L R : List Sym) (k : Nat),
      ({state := q, left := listPow x k ++ L, head := d, right := R} : Config n)
        -[tm]->*
      {state := q, left := L, head := d, right := listPow x' k ++ R} := by
  intro L R k
  induction k generalizing L R with
  | zero =>
    simp only [listPow_zero, List.nil_append]
    exact EvStep.refl
  | succ k ih =>
    -- Goal: `{listPow x (k+1) ++ L} →* {L, listPow x' (k+1) ++ R}`
    -- Step 1: `listPow x (k+1) ++ L = x ++ listPow x k ++ L`, apply h1 to get
    --         `{listPow x k ++ L, d, x' ++ R}`.
    -- Step 2: IH with L := L, R := x' ++ R gives
    --         `{listPow x k ++ L, d, x' ++ R} →* {L, d, listPow x' k ++ (x' ++ R)}`.
    -- Step 3: Rewrite `listPow x' k ++ (x' ++ R) = listPow x' (k+1) ++ R` using
    --         `listPow_succ_right` + associativity.
    rw [listPow_succ, List.append_assoc]
    refine EvStep.trans (h1 (listPow x k ++ L) R) ?_
    have ih' := ih L (x' ++ R)
    rw [listPow_succ_right, List.append_assoc]
    exact ih'

/-- **Right shift rule lifting (BusyCoq `shift_rule_R`)**: mirror image of
    `shift_rule_L_lift` — the segment `x` on the RIGHT gets consumed and
    replaced by `x'` on the LEFT across `n` iterations. -/
theorem shift_rule_R_lift (tm : TM n) (q : Option (Fin n)) (d : Sym)
    (x x' : List Sym)
    (h1 : ∀ L R : List Sym,
      ({state := q, left := L, head := d, right := x ++ R} : Config n) -[tm]->*
      {state := q, left := x' ++ L, head := d, right := R}) :
    ∀ (L R : List Sym) (k : Nat),
      ({state := q, left := L, head := d, right := listPow x k ++ R} : Config n)
        -[tm]->*
      {state := q, left := listPow x' k ++ L, head := d, right := R} := by
  intro L R k
  induction k generalizing L R with
  | zero =>
    simp only [listPow_zero, List.nil_append]
    exact EvStep.refl
  | succ k ih =>
    rw [listPow_succ, List.append_assoc]
    refine EvStep.trans (h1 L (listPow x k ++ R)) ?_
    have ih' := ih (x' ++ L) R
    rw [listPow_succ_right, List.append_assoc]
    exact ih'

/-! ### Connecting `listPow` with existing tape atoms

These theorems let users pass their existing `rev_zebra`, `zebra`, `ones`,
`zeros` lemmas through the lifting machinery. -/

open BusyLean

theorem listPow_true_eq_ones (k : Nat) : listPow [true] k = ones k := by
  induction k with
  | zero => rfl
  | succ k ih => show [true] ++ listPow [true] k = true :: ones k; rw [ih]; rfl

theorem listPow_false_eq_zeros (k : Nat) : listPow [false] k = zeros k := by
  induction k with
  | zero => rfl
  | succ k ih => show [false] ++ listPow [false] k = false :: zeros k; rw [ih]; rfl

end BusyLean

