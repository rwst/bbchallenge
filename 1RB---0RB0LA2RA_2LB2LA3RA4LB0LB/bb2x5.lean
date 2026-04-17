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
  let some (_, hLhs, _) := hType.eq?
    | throwError "tm_follow: hypothesis is not an equality"
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
-- Generic symbol list helpers
-- ============================================================

/-- Repeat a symbol `n` times. -/
def rep (s : Sym) (n : Nat) : List Sym := List.replicate n s

@[simp] theorem rep_zero (s : Sym) : rep s 0 = [] := rfl
@[simp] theorem rep_succ (s : Sym) (n : Nat) : rep s (n + 1) = s :: rep s n := rfl

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

end BB2x5
