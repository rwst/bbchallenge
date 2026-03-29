/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.TapeHelpers
import BusyLean.RunLemmas

/-!
# BusyLean: Infinite (Stream-based) Tape Definitions

Provides `SConfig` — a Turing machine configuration with infinite tapes
represented as functions `Nat → Sym`. This eliminates the need for
`RightPadEquiv` padding infrastructure in symbolic proofs.

The list-based `Config` remains for `decide`-based concrete proofs.
A commutativity theorem `toSConfig_run` bridges the two representations.

## Design (following BusyCoq)

BusyCoq uses coinductive `Stream` for tapes with `const 0` as blank.
We use `Nat → Sym` which is equivalent and simpler in Lean 4.

## Key definitions

- `Side` — `Nat → Sym`, an infinite half-tape
- `SConfig n` — stream-based TM configuration
- `sstep` / `srun` — step/run on stream configs
- `Config.toSConfig` — embed list config into stream config
- `toSConfig_step` / `toSConfig_run` — commutativity theorems
- `snonhalt_of_progress` — non-halting via progress invariant on stream configs

## Notation

- `0∞` — blank side (all false/0)
- `xs *> s` — prepend list `xs` to side `s`
-/

namespace BusyLean

/-! ### Side (infinite half-tape) -/

/-- An infinite half-tape: `Nat → Sym`. Index 0 is closest to the head. -/
abbrev Side := Nat → Sym

namespace Side

/-- The blank side: all false (0). Equivalent to BusyCoq's `const 0`. -/
def blank : Side := fun _ => false

/-- Prepend a symbol to a side. -/
def cons (x : Sym) (s : Side) : Side
  | 0 => x
  | n + 1 => s n

/-- Head of a side (index 0). -/
abbrev head (s : Side) : Sym := s 0

/-- Tail of a side (shift by 1). -/
def tail (s : Side) : Side := fun n => s (n + 1)

/-- Prepend a list of symbols to a side. -/
def prepend : List Sym → Side → Side
  | [], s => s
  | x :: xs, s => cons x (prepend xs s)

/-! #### Simp lemmas -/

@[simp] theorem cons_zero (x : Sym) (s : Side) : cons x s 0 = x := rfl
@[simp] theorem cons_succ (x : Sym) (s : Side) (n : Nat) : cons x s (n + 1) = s n := rfl

@[simp] theorem head_cons (x : Sym) (s : Side) : head (cons x s) = x := rfl
@[simp] theorem tail_cons (x : Sym) (s : Side) : tail (cons x s) = s := by
  ext n; simp [tail, cons]

@[simp] theorem head_blank : head blank = false := rfl
@[simp] theorem tail_blank : tail blank = blank := by
  ext n; simp [tail, blank]

@[simp] theorem prepend_nil (s : Side) : prepend [] s = s := rfl
@[simp] theorem prepend_cons (x : Sym) (xs : List Sym) (s : Side) :
    prepend (x :: xs) s = cons x (prepend xs s) := rfl

@[simp] theorem head_prepend_cons (x : Sym) (xs : List Sym) (s : Side) :
    head (prepend (x :: xs) s) = x := rfl

@[simp] theorem tail_prepend_cons (x : Sym) (xs : List Sym) (s : Side) :
    tail (prepend (x :: xs) s) = prepend xs s := tail_cons x _

@[simp] theorem prepend_append (xs ys : List Sym) (s : Side) :
    prepend (xs ++ ys) s = prepend xs (prepend ys s) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

-- ones/zeros integration
@[simp] theorem prepend_ones_zero (s : Side) : prepend (ones 0) s = s := rfl
@[simp] theorem prepend_ones_succ (n : Nat) (s : Side) :
    prepend (ones (n + 1)) s = cons true (prepend (ones n) s) := rfl
@[simp] theorem prepend_zeros_zero (s : Side) : prepend (zeros 0) s = s := rfl
@[simp] theorem prepend_zeros_succ (n : Nat) (s : Side) :
    prepend (zeros (n + 1)) s = cons false (prepend (zeros n) s) := rfl

-- blank absorption: prepending zeros to blank is still blank
@[simp] theorem prepend_zeros_blank (n : Nat) : prepend (zeros n) blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => ext k; cases k <;> simp [ih, blank]

end Side

/-! ### Stream-based configuration -/

/-- Configuration with infinite (stream-based) tapes.
    Equivalent to BusyCoq's `Q * tape` where `tape = side * Sym * side`. -/
structure SConfig (n : Nat) where
  /-- Current state, or `none` if halted -/
  state : Option (Fin n)
  /-- Tape cells to the left of head (index 0 = immediately left) -/
  left  : Side
  /-- Symbol currently under the head -/
  head  : Sym
  /-- Tape cells to the right of head (index 0 = immediately right) -/
  right : Side

@[ext]
theorem SConfig.ext {n : Nat} {c₁ c₂ : SConfig n}
    (hs : c₁.state = c₂.state) (hl : c₁.left = c₂.left)
    (hh : c₁.head = c₂.head) (hr : c₁.right = c₂.right) :
    c₁ = c₂ := by
  cases c₁; cases c₂; simp at *; exact ⟨hs, hl, hh, hr⟩

/-- Whether a stream configuration is halted. -/
def SConfig.halted {n : Nat} (c : SConfig n) : Prop := c.state = none

instance {n : Nat} (c : SConfig n) : Decidable c.halted :=
  inferInstanceAs (Decidable (c.state = none))

/-! ### Step and Run -/

/-- Execute one step on a stream configuration. -/
@[simp]
def sstep {n : Nat} (tm : TM n) (c : SConfig n) : SConfig n :=
  match c.state with
  | none => c
  | some q =>
    match tm.tr q c.head with
    | none => { state := none, left := c.left, head := c.head, right := c.right }
    | some (q', w, d) =>
      match d with
      | Dir.R =>
        { state := some q',
          left := Side.cons w c.left,
          head := c.right.head,
          right := c.right.tail }
      | Dir.L =>
        { state := some q',
          left := c.left.tail,
          head := c.left.head,
          right := Side.cons w c.right }

/-- Run the machine for `k` steps on a stream configuration. -/
def srun {n : Nat} (tm : TM n) (c : SConfig n) : Nat → SConfig n
  | 0 => c
  | k + 1 => srun tm (sstep tm c) k

/-! ### Run lemmas -/

@[simp]
theorem srun_zero {n : Nat} (tm : TM n) (c : SConfig n) : srun tm c 0 = c := rfl

theorem srun_succ {n : Nat} (tm : TM n) (c : SConfig n) (k : Nat) :
    srun tm c (k + 1) = srun tm (sstep tm c) k := rfl

theorem srun_add {n : Nat} (tm : TM n) (c : SConfig n) (a b : Nat) :
    srun tm c (a + b) = srun tm (srun tm c a) b := by
  induction a generalizing c with
  | zero => simp [srun]
  | succ a ih =>
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    rw [show srun tm c (a + 1 + b) = srun tm (sstep tm c) (a + b) from by rw [h1]; rfl]
    rw [show srun tm c (a + 1) = srun tm (sstep tm c) a from rfl]
    exact ih (sstep tm c)

@[simp]
theorem sstep_halted {n : Nat} (tm : TM n) (c : SConfig n) (h : c.halted) :
    sstep tm c = c := by
  simp [sstep, SConfig.halted] at *; simp [h]

theorem srun_halted {n : Nat} (tm : TM n) (c : SConfig n) (h : c.halted) (k : Nat) :
    srun tm c k = c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [srun_succ, sstep_halted tm c h]; exact ih c h

@[simp]
theorem srun_one {n : Nat} (tm : TM n) (c : SConfig n) : srun tm c 1 = sstep tm c := rfl

/-! ### Embedding: List configs → Stream configs -/

/-- Convert a list to a side by padding with false (blank). -/
def listToSide (l : List Sym) : Side := fun i => l.getD i false

@[simp] theorem listToSide_nil : listToSide [] = Side.blank := by
  ext n; simp [listToSide, Side.blank]

@[simp] theorem listToSide_cons (x : Sym) (xs : List Sym) :
    listToSide (x :: xs) = Side.cons x (listToSide xs) := by
  ext n; cases n <;> simp [listToSide, Side.cons]

theorem listToSide_head (l : List Sym) :
    Side.head (listToSide l) = listHead l false := by
  cases l <;> simp [listToSide, Side.head, listHead]

theorem listToSide_tail (l : List Sym) :
    Side.tail (listToSide l) = listToSide (listTail l) := by
  ext n; cases l with
  | nil => simp [listToSide, Side.tail, listTail]
  | cons x xs => simp [Side.tail]

@[simp] theorem listToSide_append (xs ys : List Sym) :
    listToSide (xs ++ ys) = Side.prepend xs (listToSide ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem listToSide_zeros (p : Nat) : listToSide (zeros p) = Side.blank := by
  ext n; simp [listToSide, Side.blank, zeros]
  simp [List.getD, List.getElem?_replicate]
  split <;> rfl

@[simp] theorem listToSide_ones (n : Nat) :
    listToSide (ones n) = Side.prepend (ones n) Side.blank := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

@[simp] theorem listToSide_ones_zeros (n p : Nat) :
    listToSide (ones n ++ zeros p) = Side.prepend (ones n) Side.blank := by
  simp

/-- Embed a list-based config into a stream-based config.
    Finite tapes are extended with blanks (false). -/
def Config.toSConfig {n : Nat} (c : Config n) : SConfig n where
  state := c.state
  left := listToSide c.left
  head := c.head
  right := listToSide c.right

theorem toSConfig_state {n : Nat} (c : Config n) :
    c.toSConfig.state = c.state := rfl

/-- Stepping commutes with the embedding. -/
theorem toSConfig_step {n : Nat} (tm : TM n) (c : Config n) :
    (step tm c).toSConfig = sstep tm c.toSConfig := by
  cases c with | mk st l h r =>
  simp only [Config.toSConfig]
  cases st with
  | none => rfl
  | some q =>
    simp only [step, sstep]
    cases tm.tr q h with
    | none => rfl
    | some val =>
      obtain ⟨q', w, d⟩ := val
      cases d <;> (ext <;> simp [listToSide_head, listToSide_tail])

/-- Running commutes with the embedding. -/
theorem toSConfig_run {n : Nat} (tm : TM n) (c : Config n) (k : Nat) :
    (run tm c k).toSConfig = srun tm c.toSConfig k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [run_succ, srun_succ, ← toSConfig_step]
    exact ih (step tm c)

/-! ### Properties derivable from listToSide equality -/

theorem listToSide_getD (l : List Sym) (i : Nat) :
    listToSide l i = l.getD i false := rfl

/-- If two lists have the same stream embedding, they agree at every index. -/
theorem getD_eq_of_listToSide_eq {R₁ R₂ : List Sym}
    (h : listToSide R₁ = listToSide R₂) (i : Nat) :
    R₁.getD i false = R₂.getD i false := by
  have : listToSide R₁ i = listToSide R₂ i := by rw [h]
  exact this

/-- A list whose stream embedding is blank must be all-false. -/
theorem all_false_of_listToSide_blank {R : List Sym}
    (h : listToSide R = Side.blank) : R.all (!·) = true := by
  induction R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true]
    have h0 : listToSide (x :: xs) 0 = Side.blank 0 := by rw [h]
    have htl : listToSide xs = Side.blank := by
      ext n; have := show listToSide (x :: xs) (n + 1) = Side.blank (n + 1) by rw [h]
      simpa [listToSide, Side.blank] using this
    constructor
    · simp [listToSide, Side.blank] at h0; cases x <;> simp_all
    · exact ih htl

/-! ### Padding independence via stream embedding -/

/-- Two list configs that differ only in right-tape trailing-zero padding
    map to the same stream config. This replaces the entire `RightPadEquiv`
    infrastructure from the list-based approach. -/
theorem toSConfig_padding_indep {n : Nat} (c₁ c₂ : Config n)
    (hs : c₁.state = c₂.state) (hl : c₁.left = c₂.left)
    (hh : c₁.head = c₂.head) (hr : listToSide c₁.right = listToSide c₂.right) :
    c₁.toSConfig = c₂.toSConfig := by
  ext <;> simp [Config.toSConfig, *]

/-- Running two padding-equivalent configs gives the same stream result. -/
theorem run_toSConfig_of_eq {m : Nat} (tm : TM m) (c₁ c₂ : Config m) (k : Nat)
    (h : c₁.toSConfig = c₂.toSConfig) :
    (run tm c₁ k).toSConfig = (run tm c₂ k).toSConfig := by
  rw [toSConfig_run, toSConfig_run, h]

/-! ### Non-halting from stream configs -/

/-- If a stream config never halts, the corresponding list config never halts. -/
theorem nonhalt_of_sconfig {n : Nat} (tm : TM n) (c : Config n)
    (h : ∀ m, (srun tm c.toSConfig m).state ≠ none) :
    ∀ m, (run tm c m).state ≠ none := by
  intro m hm
  exact h m (by rw [← toSConfig_run]; simp [Config.toSConfig, hm])

/-! ### Non-halting by progress invariant (stream version) -/

private theorem srun_state_none {n : Nat} (tm : TM n) (c : SConfig n) (m : Nat)
    (h : c.state = none) : (srun tm c m).state = none := by
  rw [srun_halted tm c h]; exact h

private theorem srun_alive_of_later {n : Nat} (tm : TM n) (c : SConfig n) (m k : Nat)
    (hmk : m ≤ k) (hk : (srun tm c k).state ≠ none) :
    (srun tm c m).state ≠ none :=
  fun hm => hk (by rw [show k = m + (k - m) from by omega, srun_add]
                   exact srun_state_none tm _ _ hm)

/-- **Non-halting by progress invariant (stream version).**

If `P` is a predicate on stream configurations such that every `P`-configuration
can advance at least one step to another `P`-configuration with non-halted state,
then any `P`-configuration never halts.

This is the stream-tape analogue of `nonhalt_of_progress`. -/
theorem snonhalt_of_progress {n : Nat} (tm : TM n) (P : SConfig n → Prop)
    (hprog : ∀ c, P c → ∃ k, 0 < k ∧ P (srun tm c k) ∧ (srun tm c k).state ≠ none)
    (c : SConfig n) (hc : P c) : ∀ m, (srun tm c m).state ≠ none := by
  intro m
  induction m using Nat.strongRecOn generalizing c with
  | _ m ihm =>
    match m with
    | 0 =>
      obtain ⟨k, _, _, hk_state⟩ := hprog c hc
      exact srun_alive_of_later tm c 0 k (Nat.zero_le _) hk_state
    | .succ m' =>
      obtain ⟨k, hk_pos, hk_P, hk_state⟩ := hprog c hc
      by_cases hge : m'.succ ≤ k
      · exact srun_alive_of_later tm c m'.succ k hge hk_state
      · rw [show m'.succ = k + (m'.succ - k) from by omega, srun_add]
        exact ihm (m'.succ - k) (by omega) (srun tm c k) hk_P

/-! ### Initial configuration -/

/-- Initial stream configuration: state 0, blank tape. -/
def sinitConfig (n : Nat) (h : 0 < n := by omega) : SConfig n where
  state := some ⟨0, h⟩
  left := Side.blank
  head := false
  right := Side.blank

theorem toSConfig_initConfig (n : Nat) (h : 0 < n) :
    (initConfig n h).toSConfig = sinitConfig n h := by
  simp [initConfig, sinitConfig, Config.toSConfig]

/-! ### Notation -/

/-- Blank side (all false/0). Equivalent to BusyCoq's `const 0`. -/
scoped notation "blank∞" => Side.blank

/-- Prepend a list to a side: `xs *> s`.
    Equivalent to BusyCoq's `xs *> r` / `Str_app`. -/
scoped infixr:25 " *> " => Side.prepend

end BusyLean
