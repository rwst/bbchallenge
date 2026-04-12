/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Inspired by Busybeaver.Deciders.BackwardsReasoning
  (https://github.com/mfornet/busybeaver)
Original authors: mfornet et al.
Adapted to BusyLean zipper tape model.
-/
import BusyLean.Defs
import BusyLean.RunLemmas
import BusyLean.Transition

/-!
# BusyLean: Backward Reasoning

Proves non-halting by showing that all halting transitions are unreachable
via backward symbolic search. A `SymConfig` represents a set of concrete
configs (with wildcard tape cells). Starting from each halting (state, symbol)
pair, we step *backwards* through all possible predecessors. If the search
tree dies out within `bound` steps, no config can reach the halting transition
in that many steps.

## Key definitions

- `SymConfig n` — symbolic config with wildcard tape cells
- `matchingConfig?` — reverse a single transition
- `backwardStep` — all predecessor symbolic configs
- `backwardReason` — recursive backward search (computable `Bool`)
- `backwardReason_correct` — soundness theorem
-/

namespace BusyLean

variable {n : Nat}

/-! ### Symbolic cells and tape matching -/

/-- A symbolic cell: `none` = wildcard, `some s` = known value. -/
abbrev SymSym := Option Sym

/-- Symbolic TM configuration for backward reasoning.
    State and head are always known; left/right tape cells may be wildcards. -/
structure SymConfig (n : Nat) where
  state : Fin n
  left  : List SymSym
  head  : Sym
  right : List SymSym
  deriving DecidableEq, BEq

/-- Create a symbolic config from a halting transition (state, symbol).
    All tape cells are wildcards. -/
@[inline]
def SymConfig.fromTrans (q : Fin n) (s : Sym) : SymConfig n :=
  { state := q, left := [], head := s, right := [] }

/-- Does a symbolic cell match a concrete cell? -/
@[inline]
def cellMatch (sc : SymSym) (cc : Sym) : Bool :=
  match sc with
  | none => true
  | some s => s == cc

/-- Does a symbolic tape match a concrete tape?
    Concrete cells beyond the list are `false` (blank).
    Symbolic cells beyond the list are `none` (wildcard, always match). -/
def tapeMatch : List SymSym → List Sym → Bool
  | [], _ => true
  | sc :: ss, [] => cellMatch sc false && tapeMatch ss []
  | sc :: ss, c :: cs => cellMatch sc c && tapeMatch ss cs

/-- Does the symbolic config match the concrete config? -/
def SymConfig.matches (sc : SymConfig n) (c : Config n) : Prop :=
  c.state = some sc.state ∧
  sc.head = c.head ∧
  tapeMatch sc.left c.left = true ∧
  tapeMatch sc.right c.right = true

/-! ### Backward step -/

/-- Reverse a single transition from symbolic config `sc`.

    Given candidate predecessor transition `tm.tr q s = some (q', w, d)`:
    - `q'` must equal `sc.state` (result state matches)
    - the cell where `w` was written must be wildcard or equal `w` in `sc`
    - the predecessor config has state `q`, head `s`, and tapes reconstructed
      by undoing the move -/
def matchingConfig? (tm : TM n) (sc : SymConfig n) (q : Fin n) (s : Sym) :
    Option (SymConfig n) :=
  match tm.tr q s with
  | none => none
  | some (q', w, d) =>
    if q' ≠ sc.state then none
    else match d with
    | Dir.R =>
      -- Forward: {q, L, s, r::R} → {q', w::L, r, R}
      -- sc represents the AFTER config. Check written cell:
      -- sc.left.head? is Option (Option Sym):
      --   none = list empty (wildcard), some none = cell is wildcard, some (some w) = matches
      let lh := sc.left.head?
      if lh = none ∨ lh = some none ∨ lh = some (some w) then
        some { state := q,
               left := sc.left.tail,
               head := s,
               right := some sc.head :: sc.right }
      else none
    | Dir.L =>
      -- Forward: {q, l::L, s, R} → {q', L, l, w::R}
      let rh := sc.right.head?
      if rh = none ∨ rh = some none ∨ rh = some (some w) then
        some { state := q,
               left := some sc.head :: sc.left,
               head := s,
               right := sc.right.tail }
      else none

/-- All possible predecessor symbolic configs of `sc`. -/
def backwardStep (tm : TM n) (sc : SymConfig n) : List (SymConfig n) :=
  (List.finRange n).flatMap fun q =>
    [false, true].filterMap fun s =>
      matchingConfig? tm sc q s

/-- Recursive backward reasoning: returns `true` if `sc` is provably
    unreachable in `bound` forward steps.

    - `bound = 0`: can't prove unreachability (return `false`)
    - `bound = k+1`: check that every predecessor is unreachable in `k` steps -/
def backwardReason : Nat → TM n → SymConfig n → Bool
  | 0, _, _ => false
  | k + 1, tm, sc => (backwardStep tm sc).all (backwardReason k tm)

/-! ### Correctness -/

/-- `fromTrans q s` matches any config with state `some q` and head `s`. -/
theorem SymConfig.fromTrans_matches (q : Fin n) (s : Sym) (c : Config n)
    (hq : c.state = some q) (hs : c.head = s) :
    (SymConfig.fromTrans q s).matches c :=
  ⟨hq, hs.symm, rfl, rfl⟩

/-- Core completeness: if `step tm c = c'`, `c` is not halted, and `sc`
    matches `c'`, then `matchingConfig?` with `c`'s state and head returns
    a symbolic config matching `c`.

    This is the key lemma connecting forward steps to backward search. -/
theorem matchingConfig?_correct (tm : TM n) (c c' : Config n) (sc : SymConfig n)
    (q : Fin n) (hq : c.state = some q)
    (hstep : step tm c = c')
    (hmatch : sc.matches c') :
    ∃ sc' : SymConfig n,
      matchingConfig? tm sc q c.head = some sc' ∧ sc'.matches c := by
  obtain ⟨hst, hhd, hleft, hright⟩ := hmatch
  simp only [step, hq] at hstep
  cases htr : tm.tr q c.head with
  | none =>
    simp only [htr] at hstep; rw [← hstep] at hst; simp at hst
  | some val =>
    obtain ⟨q', w, d⟩ := val
    simp only [htr] at hstep
    unfold matchingConfig?; rw [htr]
    -- Split by direction, then common setup
    cases d <;> simp only [] at hstep <;> (
      rw [← hstep] at hst hhd hleft hright; clear hstep;
      simp only at hst hhd hleft hright;
      have hqeq : q' = sc.state := by cases hst; rfl;
      subst hqeq;
      simp only [ne_eq, not_true_eq_false, ↓reduceIte])
    · -- Dir.L: hright has w :: c.right, hleft/hhd have listTail/listHead c.left
      -- Show the if-condition holds
      have hrh : sc.right.head? = none ∨ sc.right.head? = some none ∨
          sc.right.head? = some (some w) := by
        cases hsr : sc.right with
        | nil => left; rfl
        | cons x xs =>
          rw [hsr] at hright
          simp only [List.head?_cons, tapeMatch, Bool.and_eq_true] at hright ⊢
          cases x with
          | none => right; left; rfl
          | some s' =>
            right; right
            simp [cellMatch, beq_iff_eq] at hright; exact hright.1 ▸ rfl
      rw [if_pos hrh]
      refine ⟨_, rfl, hq, rfl, ?_, ?_⟩
      · -- tapeMatch (some sc.head :: sc.left) c.left
        cases hcl : c.left with
        | nil =>
          rw [hcl] at hhd hleft; simp [listHead, listTail] at hhd hleft
          simp [tapeMatch, cellMatch, hhd, hleft]
        | cons l ls =>
          rw [hcl] at hhd hleft; simp [listHead, listTail] at hhd hleft
          simp [tapeMatch, cellMatch, hhd, hleft]
      · -- tapeMatch sc.right.tail c.right
        cases hsr : sc.right with
        | nil => simp [tapeMatch]
        | cons _ xs =>
          rw [hsr] at hright
          simp only [List.tail_cons, tapeMatch, Bool.and_eq_true] at hright ⊢
          exact hright.2
    · -- Dir.R: hleft has w :: c.left, hright/hhd have listTail/listHead c.right
      have hlh : sc.left.head? = none ∨ sc.left.head? = some none ∨
          sc.left.head? = some (some w) := by
        cases hsl : sc.left with
        | nil => left; rfl
        | cons x xs =>
          rw [hsl] at hleft
          simp only [List.head?_cons, tapeMatch, Bool.and_eq_true] at hleft ⊢
          cases x with
          | none => right; left; rfl
          | some s' =>
            right; right
            simp [cellMatch, beq_iff_eq] at hleft; exact hleft.1 ▸ rfl
      rw [if_pos hlh]
      refine ⟨_, rfl, hq, rfl, ?_, ?_⟩
      · -- tapeMatch sc.left.tail c.left
        cases hsl : sc.left with
        | nil => simp [tapeMatch]
        | cons _ xs =>
          rw [hsl] at hleft
          simp only [List.tail_cons, tapeMatch, Bool.and_eq_true] at hleft ⊢
          exact hleft.2
      · -- tapeMatch (some sc.head :: sc.right) c.right
        cases hcr : c.right with
        | nil =>
          rw [hcr] at hhd hright; simp [listHead, listTail] at hhd hright
          simp [tapeMatch, cellMatch, hhd, hright]
        | cons r rs =>
          rw [hcr] at hhd hright; simp [listHead, listTail] at hhd hright
          simp [tapeMatch, cellMatch, hhd, hright]

/-- Backward step completeness: if `step tm c = c'` and `sc` matches `c'`,
    then some element of `backwardStep tm sc` matches `c`. -/
theorem backwardStep_correct (tm : TM n) (c c' : Config n) (sc : SymConfig n)
    (hc : ¬ c.halted) (hstep : step tm c = c')
    (hmatch : sc.matches c') :
    ∃ sc' ∈ backwardStep tm sc, sc'.matches c := by
  simp [Config.halted] at hc
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨sc', hsc', hmatch'⟩ := matchingConfig?_correct tm c c' sc q hq hstep hmatch
  refine ⟨sc', ?_, hmatch'⟩
  simp only [backwardStep, List.mem_flatMap, List.mem_filterMap, List.mem_finRange,
    List.mem_cons, true_and]
  exact ⟨q, c.head, by cases c.head <;> simp, hsc'⟩

/-- Main soundness theorem: if backward reasoning succeeds from `sc` with
    budget `bound`, then no config can reach (a config matching `sc`) in
    exactly `bound` steps. -/
theorem backwardReason_correct (tm : TM n) (sc : SymConfig n) (bound : Nat)
    (hbr : backwardReason bound tm sc = true)
    (c' : Config n) (hmatch : sc.matches c') :
    ∀ c : Config n, run tm c bound ≠ c' := by
  induction bound generalizing sc c' with
  | zero => simp [backwardReason] at hbr
  | succ k ih =>
    intro c heq
    -- c' = step tm (run tm c k)
    have hck_step : step tm (run tm c k) = c' := by
      have : run tm c (k + 1) = step tm (run tm c k) := by
        rw [show k + 1 = k + 1 from rfl, run_add]; rfl
      rw [← heq]; exact this.symm
    -- run tm c k is not halted (since c' has state = some sc.state)
    have hck_alive : ¬ (run tm c k).halted := by
      intro hh
      have := hmatch.1
      simp [Config.halted] at hh
      rw [← hck_step] at this
      simp [step, hh] at this
    -- By backwardStep_correct, some sc' ∈ backwardStep matching (run tm c k)
    obtain ⟨sc', hsc'_mem, hsc'_match⟩ :=
      backwardStep_correct tm (run tm c k) c' sc hck_alive hck_step hmatch
    -- backwardReason (k+1) = backwardStep.all (backwardReason k)
    simp only [backwardReason, List.all_eq_true] at hbr
    have hbr' : backwardReason k tm sc' = true := hbr sc' hsc'_mem
    -- By IH: no config can reach (run tm c k) in k steps. Contradiction.
    exact ih sc' hbr' (run tm c k) hsc'_match c rfl

/-! ### Application to non-halting proofs -/

/-- If backward reasoning succeeds for all halting transitions within `bound`,
    and the machine doesn't halt within `bound` steps (checked separately),
    then it never halts. -/
theorem nonhalt_of_backward (tm : TM n) (hn : 0 < n) (bound : Nat)
    (h_explore : ∀ m : Nat, m ≤ bound → ¬ (run tm (initConfig n) m).halted)
    (h_backward : ∀ q : Fin n, ∀ s : Sym, tm.tr q s = none →
      backwardReason bound tm (SymConfig.fromTrans q s) = true) :
    ∀ m : Nat, ¬ (run tm (initConfig n) m).halted := by
  have h0 : ¬ (initConfig n hn).halted := by simp [initConfig, Config.halted]
  exact nonhalt_of_unreachable tm (initConfig n hn) h0 fun q s htr =>
    fun ⟨k, hq, hs⟩ => by
      -- (run tm init k) has state q and head s, with tm.tr q s = none
      -- So step tm (run tm init k) is halted
      have hkhalt : (step tm (run tm (initConfig n hn) k)).halted := by
        simp only [Config.halted, step, hq]
        rw [hs, htr]
      -- k ≥ bound (otherwise h_explore would catch the halt at k+1)
      have hkge : bound ≤ k := Nat.le_of_not_lt fun hlt => by
        have := h_explore (k + 1) (by omega)
        rw [show k + 1 = k + 1 from rfl, run_add] at this
        simp only [run_one] at this
        exact this hkhalt
      -- fromTrans matches run tm init k
      have hmatch : (SymConfig.fromTrans q s).matches (run tm (initConfig n hn) k) :=
        SymConfig.fromTrans_matches q s _ hq hs
      have hbr := h_backward q s htr
      -- run tm (run tm init (k - bound)) bound = run tm init k
      have hkeq : k = (k - bound) + bound := by omega
      have hreach : run tm (run tm (initConfig n hn) (k - bound)) bound =
          run tm (initConfig n hn) k := by
        conv => rhs; rw [hkeq]
        exact (run_add tm (initConfig n hn) (k - bound) bound).symm
      exact backwardReason_correct tm _ bound hbr _ hmatch _ hreach

end BusyLean
