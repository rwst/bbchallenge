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

section TmExec
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

/-- `tm_exec [lemmas]` repeatedly executes concrete TM steps.

    Works on goals containing `run tm c k`:
    - Equality goals: `run tm c k = c'`
    - Halt goals: `(run tm c k).state = none`

    Stops when a step can't be fully simplified (shift lemma or case split needed).
    Tries to close the goal after all concrete steps are done.

    Usage: `tm_exec [antihydra, P_Config_Pad, ones]` -/
syntax "tm_exec" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

-- Extract (tm, config, stepCount) from a `run tm c k` expression.
private def findRunParts (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  let tryExtract (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
    if x.getAppFn.constName? == some ``run then
      let args := x.getAppArgs
      if args.size ≥ 4 then some (args[1]!, args[2]!, args[3]!) else none
    else none
  tryExtract e <|> e.getAppArgs.findSome? tryExtract

private def findRunInExpr (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  (findRunParts e).map fun (_, c, k) => (c, k)

-- Decrement a Nat expression by 1, avoiding Nat.sub (which is opaque to omega).
-- E.g., `2*n + 12` → `2*n + 11`, `n + 1` → `n`, `5` → `4`.
private def getNatLit? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    -- Handle @OfNat.ofNat Nat n inst
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

private partial def decNatExpr (e : Lean.Expr) : Option Lean.Expr :=
  if let some n := getNatLit? e then
    if n > 0 then some (mkNatLit (n - 1)) else none
  else if e.isAppOfArity ``HAdd.hAdd 6 then
    let a := e.getArg! 4
    let b := e.getArg! 5
    if let some b' := decNatExpr b then
      if getNatLit? b' == some 0 then some a
      else some (mkApp6 e.getAppFn (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) (e.getArg! 3) a b')
    else none
  else if e.isAppOfArity ``Nat.add 2 then
    let a := e.getArg! 0
    let b := e.getArg! 1
    if let some b' := decNatExpr b then
      if getNatLit? b' == some 0 then some a
      else some (mkApp2 (.const ``Nat.add []) a b')
    else none
  else none

elab_rules : tactic
  | `(tactic| tm_exec [$lemmas,*]) => do
    for _ in List.range 200 do
      -- Quick close attempts
      try evalTactic (← `(tactic| rfl)); return catch _ => pure ()
      try evalTactic (← `(tactic| (simp only [run_zero]; rfl))); return catch _ => pure ()
      -- Peel one step: split off 1 step via run_add, simplify in a conv
      let saved ← saveState
      try
        let goalType ← (← getMainGoal).getType
        let some (_, lhs, _) := goalType.eq? | throwError ""
        let some (_, kExpr) := findRunInExpr lhs | throwError ""
        let some kMinus1Expr := decNatExpr kExpr | throwError ""
        let kSyn ← Term.exprToSyntax kExpr
        let kMinus1Syn ← Term.exprToSyntax kMinus1Expr
        -- Split: k = 1 + (k-1), then run_add gives run tm (run tm c 1) (k-1)
        evalTactic (← `(tactic|
          rw [show $kSyn = 1 + $kMinus1Syn from by omega, run_add]))
        -- Simplify just the inner (run tm c 1) via conv, keeping tm folded in outer run
        -- Use positional navigation (arg 1; arg 2) to target the config of the outer run,
        -- avoiding ambiguity when k-1 = 1 (both inner and outer would match `run _ _ 1`)
        evalTactic (← `(tactic|
          conv =>
            lhs
            enter [2]
            simp (config := { decide := true }) [run, step,
              ones_succ, zeros_succ,
              $lemmas,*]))
        -- Check if conv closed the goal (unlikely but possible)
        if (← getGoals).isEmpty then return
        -- Fold leading true/false conses back into ones/zeros form
        try evalTactic (← `(tactic|
          simp only [ones_cons_append, zeros_cons_append, ← ones_succ, ← zeros_succ]))
        catch _ => pure ()
        -- Check if this closed the goal
        if (← getGoals).isEmpty then return
        -- Verify progress: config must be a fully reduced struct with concrete head
        let goalType ← (← getMainGoal).getType
        let some (_, lhs, _) := goalType.eq? | throwError ""
        let some (config, _) := findRunInExpr lhs | throwError ""
        let fn := config.getAppFn
        unless fn.isConst && fn.constName!.isStr && fn.constName!.getString! == "mk" do
          throwError ""
        let configArgs := config.getAppArgs
        unless configArgs.size > 3 && configArgs[3]!.isConst do throwError ""
      catch _ => do saved.restore; break
    -- Post-loop: try to close the goal if remaining steps = 0
    try
      let goalType ← (← getMainGoal).getType
      let some (_, lhs, _) := goalType.eq? | throwError ""
      let some (_, kExpr) := findRunInExpr lhs | throwError ""
      let kSyn ← Term.exprToSyntax kExpr
      evalTactic (← `(tactic| simp only [show $kSyn = 0 from by omega, run_zero]))
      try evalTactic (← `(tactic| rfl)); return catch _ => pure ()
      evalTactic (← `(tactic|
        simp (config := { decide := true }) [
          ones, zeros, ones_succ, zeros_succ, ones_zero, zeros_zero,
          ones_append, zeros_append,
          List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
          $lemmas,*]))
    catch _ => pure ()
    -- If goal still open, check if it's a halt goal (not a run equality)
    -- Only try aggressive simp for halt goals like (run tm c k).state = none
    if !(← getGoals).isEmpty then
      let goalType ← (← getMainGoal).getType
      -- Guard: only try halt-close if goal is NOT `run tm c k = c'`
      let isRunEq := match goalType.eq? with
        | some (_, lhs, _) => (findRunInExpr lhs).isSome
        | none => false
      unless isRunEq do
        try evalTactic (← `(tactic|
          simp (config := { decide := true }) [
            run, step, run_halted, Config.halted,
            listHead, listTail,
            ones, zeros, ones_succ, zeros_succ, ones_zero, zeros_zero,
            ones_append, zeros_append,
            List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
            $lemmas,*]))
        catch _ => pure ()

end TmExec

end BusyLean
