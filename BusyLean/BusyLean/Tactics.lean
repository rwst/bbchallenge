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

- `tm_chain` — Automatically prove `run tm c k = c'` by splitting into chunks
  (default 10) and proving each with `decide`. Usage: `tm_chain` or `tm_chain 20`.
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
    let goal ← getMainGoal
    -- Look up h in the local context (not elabTerm, which misses local hyps)
    let hName := h.getId
    let lctx := (← goal.getDecl).lctx
    let some decl := lctx.findFromUserName? hName
      | throwError "tm_follow: unknown hypothesis '{hName}'"
    let hType := decl.type
    -- hType should be: run tm c₁ k₁ = c₂
    let_expr Eq _ lhs _ := hType | throwError "tm_follow: hypothesis '{hName}' is not an equality"
    -- lhs = run tm c₁ k₁ — extract k₁ as an Expr (not evaluated to Nat)
    let .app (.app (.app _ _tm) _c1) k1Expr := lhs
      | throwError "tm_follow: hypothesis LHS not of the form `run tm c k`"
    -- Get the goal: run tm c₁ k = c₃ — extract k
    let goalType ← goal.getType
    let_expr Eq _ goalLhs _ := goalType | throwError "tm_follow: goal not an equality"
    let .app (.app (.app _ _) _) kExpr := goalLhs
      | throwError "tm_follow: goal LHS not of the form `run tm c k`"
    -- Rewrite: k = k₁ + (k - k₁) by omega, then run_add, then h
    -- Keeps step counts symbolic — omega handles the arithmetic
    let kSyn ← Term.exprToSyntax kExpr
    let k1Syn ← Term.exprToSyntax k1Expr
    evalTactic (← `(tactic|
      (rw [show $kSyn = $k1Syn + ($kSyn - $k1Syn) from by omega, run_add]; rw [$h:ident])))
    -- If remaining steps = 0 (symbolically), try to close: normalize step count, then rfl
    try evalTactic (← `(tactic| rfl)) catch _ =>
    try evalTactic (← `(tactic| (simp only [show $kSyn - $k1Syn = 0 from by omega, run]; rfl)))
      catch _ => pure ()

/-- `tm_chain` automatically proves `run tm c k = c'` by splitting into chunks
    and proving each with `decide`.

    Usage: `tm_chain` (default chunk size 10) or `tm_chain 20` for custom chunk size.

    This automates the manual pattern of defining intermediate theorems and
    chaining them with `tm_follow`. -/
syntax "tm_chain" (num)? : tactic

open Lean Elab Tactic Meta in
private def extractRunGoal (goalType : Expr) :
    MetaM (Expr × Expr × Expr × Expr) := do
  let_expr Eq _ goalLhs goalRhs := goalType
    | throwError "tm_chain: goal is not an equality"
  let .app (.app (.app _ tmExpr) cExpr) kExpr := goalLhs
    | throwError "tm_chain: goal LHS not of the form `run tm c k`"
  return (tmExpr, cExpr, kExpr, goalRhs)

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| tm_chain $[$n?]?) => do
    let chunkSize := match n? with
      | some n => n.getNat
      | none => 10
    if chunkSize == 0 then throwError "tm_chain: chunk size must be > 0"
    let goal ← getMainGoal
    let goalType ← goal.getType
    let (_, _, kExpr, _) ← extractRunGoal goalType
    let some kNat ← evalNat kExpr |>.run
      | throwError "tm_chain: can't evaluate step count"
    if kNat == 0 then
      evalTactic (← `(tactic| rfl))
      return
    if kNat ≤ chunkSize then
      evalTactic (← `(tactic| decide))
      return
    -- Chain: repeatedly split off chunks and prove each with decide
    let mut remaining := kNat
    while remaining > chunkSize do
      let chunk := chunkSize
      let rest := remaining - chunk
      -- Get fresh goal state
      let curGoal ← getMainGoal
      let curType ← curGoal.getType
      let (tmExpr, cExpr, curKExpr, _) ← extractRunGoal curType
      let curKSyn ← Term.exprToSyntax curKExpr
      let chunkSyn ← Term.exprToSyntax (mkNatLit chunk)
      let restSyn ← Term.exprToSyntax (mkNatLit rest)
      -- Evaluate run tm c chunk to get intermediate config
      let runChunkExpr ← mkAppM ``run #[tmExpr, cExpr, mkNatLit chunk]
      let cNext ← reduce runChunkExpr
      let cNextSyn ← Term.exprToSyntax cNext
      -- Split and rewrite:
      -- 1. rw total = chunk + rest
      -- 2. rw run_add to get run tm (run tm c chunk) rest
      -- 3. have h : run tm c chunk = cNext := by decide; rw [h]
      let hName := Name.mkSimple s!"_chain_{remaining}"
      let hIdent := mkIdent hName
      evalTactic (← `(tactic|
        rw [show $curKSyn = $chunkSyn + $restSyn from by omega]))
      evalTactic (← `(tactic| rw [run_add]))
      let tmSyn ← Term.exprToSyntax tmExpr
      let cSyn ← Term.exprToSyntax cExpr
      evalTactic (← `(tactic|
        have $hIdent : run $tmSyn $cSyn $chunkSyn = $cNextSyn := by decide))
      evalTactic (← `(tactic| rw [$hIdent:ident]))
      evalTactic (← `(tactic| clear $hIdent))
      remaining := rest
    -- Final chunk
    evalTactic (← `(tactic| decide))

end BusyLean
