import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic

/-!
# BB2x5 — 2-state 5-symbol Turing machine framework

Generic infrastructure for 2-state, 5-symbol Busy Beaver proofs. Mirrors the
shape of `BusyLean` (binary alphabet) but with `Sym := Fin 5` and `St := Fin 2`.

Provides:
- `Config`, `step`, `run`, `run_add`, `run_halted`, `run_alive_of_later`
- `nonhalt_of_progress` (progress-invariant non-halting)
- `Multistep` notation `A -[tr]{k}-> B` with `Trans` instance for `calc`
- `tm_follow` tactic (BusyLean-style): peel a prefix of `run` via a lemma
-/

set_option autoImplicit false

namespace BB2x5

inductive Dir where | L | R
  deriving DecidableEq, Repr

abbrev Sym := Fin 5

@[reducible] def s0 : Sym := 0
@[reducible] def s1 : Sym := 1
@[reducible] def s2 : Sym := 2
@[reducible] def s3 : Sym := 3
@[reducible] def s4 : Sym := 4

abbrev St := Fin 2

@[reducible] def stA : St := 0
@[reducible] def stB : St := 1

structure Config where
  state : Option St
  head  : Sym
  left  : List Sym
  right : List Sym
  deriving DecidableEq, Repr

def Config.halted (c : Config) : Prop := c.state = none

def listHd (l : List Sym) : Sym := l.headD 0
def listTl (l : List Sym) : List Sym := l.tail

@[simp] theorem listHd_cons (x : Sym) (xs : List Sym) : listHd (x :: xs) = x := rfl
@[simp] theorem listHd_nil : listHd ([] : List Sym) = 0 := rfl
@[simp] theorem listTl_cons (x : Sym) (xs : List Sym) : listTl (x :: xs) = xs := rfl
@[simp] theorem listTl_nil : listTl ([] : List Sym) = [] := rfl

/-- Transition function type. `none` means halt. -/
abbrev Tr := St → Sym → Option (St × Sym × Dir)

/-- One step of a 2-state 5-symbol TM. -/
def step (tr : Tr) (c : Config) : Config :=
  match c.state with
  | none => c
  | some q =>
    match tr q c.head with
    | none => { state := none, head := c.head, left := c.left, right := c.right }
    | some (q', s, d) =>
      match d with
      | .R => { state := some q', head := listHd c.right,
                left := s :: c.left, right := listTl c.right }
      | .L => { state := some q', head := listHd c.left,
                left := listTl c.left, right := s :: c.right }

/-- Run a TM for `n` steps. -/
def run (tr : Tr) (c : Config) : Nat → Config
  | 0     => c
  | n + 1 => run tr (step tr c) n

@[simp] theorem run_zero (tr : Tr) (c : Config) : run tr c 0 = c := rfl

theorem run_succ (tr : Tr) (c : Config) (n : Nat) :
    run tr c (n + 1) = run tr (step tr c) n := rfl

theorem run_add (tr : Tr) (c : Config) (m n : Nat) :
    run tr c (m + n) = run tr (run tr c m) n := by
  induction m generalizing c with
  | zero => simp
  | succ m ih => simp only [Nat.succ_add, run_succ]; exact ih (step tr c)

theorem step_halted (tr : Tr) (c : Config) (h : c.state = none) : step tr c = c := by
  simp only [step]; rw [h]

theorem run_halted (tr : Tr) (c : Config) (h : c.state = none) (n : Nat) :
    run tr c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, step_halted _ _ h, ih]

theorem run_state_none (tr : Tr) (c : Config) (m : Nat) (h : c.state = none) :
    (run tr c m).state = none := by
  rw [run_halted _ _ h]; exact h

theorem run_alive_of_later (tr : Tr) (c : Config) (m k : Nat)
    (hmk : m ≤ k) (hk : (run tr c k).state ≠ none) :
    (run tr c m).state ≠ none := by
  intro hm
  apply hk
  rw [show k = m + (k - m) from by omega, run_add]
  exact run_state_none tr _ _ hm

/-- **Non-halting by progress invariant.**
If every `P`-config advances in positive steps to another non-halted `P`-config,
then the machine never halts from any `P`-config. -/
theorem nonhalt_of_progress (tr : Tr) (P : Config → Prop)
    (hprog : ∀ c, P c → ∃ k, 0 < k ∧ P (run tr c k) ∧ (run tr c k).state ≠ none)
    (c : Config) (hc : P c) : ∀ m, (run tr c m).state ≠ none := by
  intro m
  induction m using Nat.strongRecOn generalizing c with
  | _ m ihm =>
    match m with
    | 0 =>
      obtain ⟨k, _, _, hk_state⟩ := hprog c hc
      exact run_alive_of_later tr c 0 k (Nat.zero_le _) hk_state
    | m' + 1 =>
      obtain ⟨k, hk_pos, hk_P, hk_state⟩ := hprog c hc
      by_cases hge : m' + 1 ≤ k
      · exact run_alive_of_later tr c (m' + 1) k hge hk_state
      · have hlt : k < m' + 1 := Nat.lt_of_not_le hge
        rw [show m' + 1 = k + (m' + 1 - k) from by omega, run_add]
        exact ihm (m' + 1 - k) (by omega) (run tr c k) hk_P

-- ============================================================
-- Multistep notation (BusyLean-style)
-- ============================================================

/-- `A -[tr]{k}-> B` means `run tr A k = B`. -/
abbrev Multistep (tr : Tr) (k : Nat) (A B : Config) : Prop := run tr A k = B

scoped notation:50 A " -[" tr "]{" k "}-> " B => Multistep tr k A B

theorem Multistep.trans {tr : Tr} {A B C : Config} {j k : Nat}
    (h1 : A -[tr]{j}-> B) (h2 : B -[tr]{k}-> C) : A -[tr]{j + k}-> C := by
  show run tr A (j + k) = C; rw [run_add, h1]; exact h2

instance {tr : Tr} {j k : Nat} :
    Trans (Multistep tr j) (Multistep tr k) (Multistep tr (j + k)) where
  trans := Multistep.trans

/-- `A -[tr]->+ B` — reaches `B` in one or more steps, with `B` non-halted. -/
def Progress (tr : Tr) (A B : Config) : Prop :=
  ∃ k : Nat, 0 < k ∧ Multistep tr k A B ∧ ¬ B.halted

scoped notation:50 A " -[" tr "]->+ " B => Progress tr A B

theorem Progress.mk {tr : Tr} {A B : Config} {k : Nat}
    (hk : 0 < k) (h : A -[tr]{k}-> B) (hB : ¬ B.halted) : A -[tr]->+ B :=
  ⟨k, hk, h, hB⟩

/-- `A -[tr]->* B` — reaches `B` in zero or more steps. -/
def EvStep (tr : Tr) (A B : Config) : Prop :=
  ∃ k : Nat, Multistep tr k A B

scoped notation:50 A " -[" tr "]->* " B => EvStep tr A B

@[refl]
theorem EvStep.refl {tr : Tr} {A : Config} : A -[tr]->* A := ⟨0, rfl⟩

theorem EvStep.from_multistep {tr : Tr} {A B : Config} {k : Nat}
    (h : A -[tr]{k}-> B) : A -[tr]->* B := ⟨k, h⟩

theorem EvStep.trans {tr : Tr} {A B C : Config}
    (h1 : A -[tr]->* B) (h2 : B -[tr]->* C) : A -[tr]->* C := by
  obtain ⟨j, hAB⟩ := h1; obtain ⟨k, hBC⟩ := h2
  exact ⟨j + k, hAB.trans hBC⟩

theorem Progress.to_evstep {tr : Tr} {A B : Config}
    (h : A -[tr]->+ B) : A -[tr]->* B :=
  let ⟨_, _, hk, _⟩ := h; EvStep.from_multistep hk

/-- `Trans` instances so `calc` chains can mix Multistep / EvStep / Progress. -/
instance {tr : Tr} : Trans (EvStep tr) (EvStep tr) (EvStep tr) where
  trans := EvStep.trans

instance {tr : Tr} {k : Nat} : Trans (Multistep tr k) (EvStep tr) (EvStep tr) where
  trans h1 h2 := (EvStep.from_multistep h1).trans h2

instance {tr : Tr} {k : Nat} : Trans (EvStep tr) (Multistep tr k) (EvStep tr) where
  trans h1 h2 := h1.trans (EvStep.from_multistep h2)

instance {tr : Tr} : Trans (Progress tr) (EvStep tr) (EvStep tr) where
  trans h1 h2 := h1.to_evstep.trans h2

instance {tr : Tr} : Trans (Progress tr) (EvStep tr) (EvStep tr) where
  trans h1 h2 := h1.to_evstep.trans h2

instance {tr : Tr} : Trans (EvStep tr) (Progress tr) (EvStep tr) where
  trans h1 h2 := h1.trans h2.to_evstep

/-- **Non-halting via an abstract state enumeration.**

Ergonomic wrapper around `nonhalt_of_progress`: you only need an abstract state
type `C`, an embedding `f : C → Config`, and a "big step" lemma showing that
every `f c` progresses to some `f c'`. The progress invariant `∃ c, x = f c` is
synthesized automatically.

Matches the BusyCoq `progress_nonhalt_simple` idiom used for 2×5 proofs:
prove one `BigStep` lemma, apply this, done. -/
theorem progress_nonhalt_simple (tr : Tr) {C : Sort*} (f : C → Config)
    (hnext : ∀ c, ∃ c', f c -[tr]->+ f c') :
    ∀ c m, (run tr (f c) m).state ≠ none := by
  intro c m
  refine nonhalt_of_progress tr (fun x => ∃ c, x = f c) ?_ (f c) ⟨c, rfl⟩ m
  rintro x ⟨c, rfl⟩
  obtain ⟨c', k, hk, hmul, hnh⟩ := hnext c
  refine ⟨k, hk, ⟨c', hmul⟩, ?_⟩
  rw [show run tr (f c) k = f c' from hmul]; exact hnh

-- ============================================================
-- `tm_follow` tactic
-- ============================================================

-- `tm_follow h` — given `h : run tr c k1 = c'` and goal `run tr c k = target`,
-- rewrite to `run tr c' (k - k1) = target` (the split `k = k1 + (k-k1)` is
-- discharged by `omega`).
--
-- `tm_follow h rest N` — same, but split as `k = k1 + N` (omega proves the
-- equation) so the remainder stays in canonical form `N` instead of the
-- awkward `k - k1`. Use this when the subsequent proof needs `N` in
-- normalized form (e.g. to match a follow-up lemma).
--
-- 5-symbol analogue of `BusyLean.tm_follow`.
open Lean Elab Tactic Meta in
private def tmFollowCore (h : TSyntax `term) (rest? : Option (TSyntax `term)) :
    TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
  let hExpr ← Term.elabTerm h none
  let hType := (← inferType hExpr).consumeMData
  -- Accept both fully-applied equalities and forall-of-equalities (like `rw`).
  -- Strip forall binders; the inner equality may contain loose bvars, but the
  -- step-count `k1` we need is usually a closed subterm.
  let mut ty := hType
  while ty.isForall do ty := ty.bindingBody!
  let some (_, hLhs, _) := ty.eq?
    | throwError "tm_follow: hypothesis type does not reduce to an equality"
  let hLhs := hLhs.consumeMData
  unless hLhs.isAppOf ``BB2x5.run do
    throwError "tm_follow: hypothesis LHS must be `run _ _ _`"
  let hArgs := hLhs.getAppArgs
  unless hArgs.size ≥ 3 do throwError "tm_follow: malformed run in hypothesis"
  let k1 := hArgs[hArgs.size - 1]!
  let goalType := (← goal.getType).consumeMData
  let some (_, gLhs, _) := goalType.eq?
    | throwError "tm_follow: goal is not an equality"
  let gLhs := gLhs.consumeMData
  unless gLhs.isAppOf ``BB2x5.run do
    throwError "tm_follow: goal LHS must be `run _ _ _`"
  let gArgs := gLhs.getAppArgs
  unless gArgs.size ≥ 3 do throwError "tm_follow: malformed run in goal"
  let k := gArgs[gArgs.size - 1]!
  let kS ← Term.exprToSyntax k
  let k1S ← Term.exprToSyntax k1
  let hS ← Term.exprToSyntax hExpr
  let restS ← match rest? with
    | some r => pure r
    | none   => `($kS - $k1S)
  evalTactic (← `(tactic|
    rw [show $kS = $k1S + $restS from by omega, run_add, $hS:term]))
  try evalTactic (← `(tactic| rfl)) catch _ => pure ()

elab "tm_follow " h:term : tactic => tmFollowCore h none
-- `tm_follow h using N` — use N as the remainder step count (omega proves `k = k1 + N`).
elab "tm_follow " h:term " using " r:term : tactic => tmFollowCore h (some r)

-- ============================================================
-- Generic list power (`lpow`): repeat a *block* of symbols `n` times
-- ============================================================
-- Matches BusyCoq's `s ^^ n` (Individual25 and siblings). Generalizes
-- `rep` (single-symbol) and `repPair` (two-symbol block) to any block.

/-- Repeat a list `xs` `n` times as a flat list. -/
def lpow {α : Type} : List α → Nat → List α
  | _,  0     => []
  | xs, n + 1 => xs ++ lpow xs n

@[simp] theorem lpow_zero {α : Type} (xs : List α) : lpow xs 0 = [] := rfl
@[simp] theorem lpow_succ {α : Type} (xs : List α) (n : Nat) :
    lpow xs (n + 1) = xs ++ lpow xs n := rfl

theorem lpow_add {α : Type} (xs : List α) (m n : Nat) :
    lpow xs (m + n) = lpow xs m ++ lpow xs n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 from by omega, lpow_succ, lpow_succ, ih,
        List.append_assoc]

theorem lpow_mul {α : Type} (xs : List α) (m n : Nat) :
    lpow xs (m * n) = lpow (lpow xs m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : m * (n + 1) = m + m * n := by rw [Nat.mul_succ, Nat.add_comm]
    rw [hm, lpow_add, ih, ← lpow_succ]

theorem lpow_length {α : Type} (xs : List α) (n : Nat) :
    (lpow xs n).length = n * xs.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [lpow_succ, List.length_append, ih, Nat.succ_mul]; omega

theorem map_lpow {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    (lpow xs n).map f = lpow (xs.map f) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [lpow_succ, List.map_append, ih, lpow_succ]

/-- `lpow_rotate`: `lpow (a :: xs) n ++ [a] = a :: lpow (xs ++ [a]) n`. Used to
    slide a sentinel `a` from right of a repeating block to the left side. -/
theorem lpow_rotate {α : Type} (a : α) (xs : List α) (n : Nat) :
    lpow (a :: xs) n ++ [a] = a :: lpow (xs ++ [a]) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lpow_succ, List.append_assoc, ih]

-- ============================================================
-- `rep` / `repPair` as specializations of `lpow`
-- ============================================================

/-- Repeat a symbol `n` times. -/
def rep (s : Sym) (n : Nat) : List Sym := List.replicate n s

@[simp] theorem rep_zero (s : Sym) : rep s 0 = [] := rfl
@[simp] theorem rep_succ (s : Sym) (n : Nat) : rep s (n + 1) = s :: rep s n := rfl

theorem rep_eq_lpow (s : Sym) (n : Nat) : rep s n = lpow [s] n := by
  induction n with
  | zero => rfl
  | succ n ih => show s :: rep s n = [s] ++ lpow [s] n; rw [ih]; rfl

/-- Repeat a pair of symbols `n` times as a flat list. -/
def repPair (a b : Sym) : Nat → List Sym
  | 0 => []
  | n + 1 => a :: b :: repPair a b n

@[simp] theorem repPair_zero (a b : Sym) : repPair a b 0 = [] := rfl
@[simp] theorem repPair_succ (a b : Sym) (n : Nat) :
    repPair a b (n + 1) = a :: b :: repPair a b n := rfl

theorem repPair_length (a b : Sym) (n : Nat) : (repPair a b n).length = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]; omega

theorem repPair_eq_lpow (a b : Sym) (n : Nat) : repPair a b n = lpow [a, b] n := by
  induction n with
  | zero => rfl
  | succ n ih => show a :: b :: repPair a b n = [a, b] ++ lpow [a, b] n; rw [ih]; rfl

-- ============================================================
-- `tm!` — parse bbchallenge string literal into a transition function
-- ============================================================
-- Format: `"XXXXX_XXXXX"` where each `X` is a 3-character transition
-- (symbol 0..4, direction L/R, target state A/B) or `"---"` for halt.
-- Example: `tm! "1RB---0RB0LA2RA_2LB2LA3RA4LB0LB"`
-- Matches BusyCoq's `TM_from_str` (Individual25:368–427).

private def chToSym : Char → Sym
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | _   => 0

private def chToDir : Char → Dir
  | 'L' => .L | _ => .R

private def chToSt : Char → St
  | 'A' => 0 | _ => 1

private def parseTrans3 (c1 c2 c3 : Char) : Option (St × Sym × Dir) :=
  if c1 = '-' ∧ c2 = '-' ∧ c3 = '-' then none
  else some (chToSt c3, chToSym c1, chToDir c2)

private def parseFive : List Char → Option (Array (Option (St × Sym × Dir)) × List Char)
  | c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 ::
    c11 :: c12 :: c13 :: c14 :: c15 :: rest =>
    some (#[parseTrans3 c1 c2 c3, parseTrans3 c4 c5 c6, parseTrans3 c7 c8 c9,
           parseTrans3 c10 c11 c12, parseTrans3 c13 c14 c15], rest)
  | _ => none

/-- Parse a bbchallenge TM string into a transition function. On parse error,
    returns the all-halt TM. -/
def parseTM (s : String) : Tr :=
  match parseFive s.toList with
  | some (aA, '_' :: rest) =>
    match parseFive rest with
    | some (aB, _) =>
      fun q sy =>
        let arr := if q = 0 then aA else aB
        arr[sy.val]?.getD none
    | _ => fun _ _ => none
  | _ => fun _ _ => none

/-- `tm! "1RB---..._..."` parses the string at elaboration time and produces
    a transition function. Uses the standard bbchallenge convention. -/
macro "tm!" s:str : term => `(BB2x5.parseTM $s)

end BB2x5
