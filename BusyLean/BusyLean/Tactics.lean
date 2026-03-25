/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.RunLemmas
import BusyLean.TapeHelpers
import BusyLean.Notation
import Lean.Elab.Tactic

/-!
# BusyLean: Proof Tactics for BB Proofs

Domain-specific tactics inspired by BusyCoq's `step`, `follow`, `es`, `ind`.

## Tactic summary

- `tm_simp` — Simplify TM expressions (step, tape operations).

- `tm_step` — Advance one TM step in a `run tm c (k+1) = c'` goal.

- `tm_steps n` — Advance `n` concrete TM steps.

- `tm_follow h` — Apply a run-segment lemma `h : run tm c₁ k₁ = c₂`
  to rewrite `run tm c₁ (k₁ + m) = c₃` into `run tm c₂ m = c₃`.

- `tm_finish` — Close `run tm c 0 = c'` or `c = c'` goals.
-/

namespace BusyLean

/-- `tm_simp` simplifies TM expressions with the standard BusyLean lemma set. -/
macro "tm_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) [
    step, run, listHead, listTail,
    ones, zeros, ones_succ, zeros_succ, ones_zero, zeros_zero,
    ones_append, zeros_append,
    mkConfig, List.reverse_cons, List.reverse_nil, List.append_assoc,
    List.cons_append, List.nil_append, List.append_nil,
    List.replicate
  ])

/-- `tm_finish` closes a goal of the form `run tm c 0 = c'` or `c = c'`. -/
macro "tm_finish" : tactic =>
  `(tactic| first
    | rfl
    | (simp only [run]; rfl)
    | (simp only [run]; tm_simp)
    | tm_simp)

/-- Helper lemma: if k = 1 + m, then run tm c k = run tm (step tm c) m. -/
theorem run_peel {n : Nat} (tm : TM n) (c : Config n) (k m : Nat) (h : k = m + 1) :
    run tm c k = run tm (step tm c) m := by
  have h2 : k = 1 + m := by omega
  subst h2
  exact run_add tm c 1 m

/-- Helper lemma: if k = a + b, then run tm c k = run tm (run tm c a) b. -/
theorem run_split_at {n : Nat} (tm : TM n) (c : Config n) (k a b : Nat) (h : k = a + b) :
    run tm c k = run tm (run tm c a) b := by
  subst h; exact run_add tm c a b

/-- `tm_step` peels off one TM step from a `run tm c k = c'` goal.
    Rewrites `run tm c k` to `run tm (step tm c) (k-1)` and simplifies the step. -/
macro "tm_step" : tactic =>
  `(tactic| first
    | rfl
    | (rw [run_peel _ _ _ _ (by omega)]; simp only [step, run]; tm_simp))

/-- `tm_steps n` advances `n` concrete TM steps. -/
syntax "tm_steps " num : tactic
macro_rules
  | `(tactic| tm_steps 0) => `(tactic| skip)
  | `(tactic| tm_steps 1) => `(tactic| tm_step)
  | `(tactic| tm_steps $n) =>
    let n' := n.getNat - 1
    let lit := Lean.Syntax.mkNumLit (toString n')
    `(tactic| (rw [run_peel _ _ _ _ (by omega)]; simp only [step]; tm_simp; tm_steps $lit))

/-- `tm_decide` closes goals about concrete TM runs using `native_decide`.
    Works for fully concrete configurations (no variables). -/
macro "tm_decide" : tactic =>
  `(tactic| native_decide)

/-- `tm_follow h` applies a run-segment lemma to the current goal.

    Given `h : run tm c₁ k₁ = c₂` and goal `run tm c₁ k = c₃` where `k = k₁ + m`,
    rewrites to `run tm c₂ m = c₃`.

    This is the Lean equivalent of BusyCoq's `follow` tactic. -/
syntax "tm_follow " ident : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| tm_follow $h) => do
    let hExpr ← elabTerm h none
    let hType ← inferType hExpr
    -- hType should be: run tm c₁ k₁ = c₂
    -- Extract k₁ from it
    let_expr Eq _ lhs _ := hType | throwError "tm_follow: hypothesis not an equality"
    -- lhs = run tm c₁ k₁
    let .app (.app (.app _ _tm) _c1) k1Expr := lhs
      | throwError "tm_follow: LHS not of the form `run tm c k`"
    -- Get the goal: run tm c₁ k = c₃
    let goal ← getMainGoal
    let goalType ← goal.getType
    let_expr Eq _ goalLhs _ := goalType | throwError "tm_follow: goal not an equality"
    let .app (.app (.app _ _) _) kExpr := goalLhs
      | throwError "tm_follow: goal LHS not of the form `run tm c k`"
    -- Compute b = k - k₁ using evalNat
    let some k1Nat ← evalNat k1Expr |>.run | throwError "tm_follow: can't eval hypothesis step count"
    let some kNat ← evalNat kExpr |>.run | throwError "tm_follow: can't eval goal step count"
    if kNat < k1Nat then throwError "tm_follow: goal steps {kNat} < hypothesis steps {k1Nat}"
    let bNat := kNat - k1Nat
    -- Now rewrite: run tm c k = run tm (run tm c k₁) b, then apply h
    let bExpr := mkNatLit bNat
    let k1ExprLit := mkNatLit k1Nat
    -- Build proof: k = k₁ + b by omega
    evalTactic (← `(tactic| (rw [show $(← Term.exprToSyntax kExpr) = $(← Term.exprToSyntax k1ExprLit) + $(← Term.exprToSyntax bExpr) from by omega]; rw [run_add]; rw [$h:ident])))

end BusyLean
