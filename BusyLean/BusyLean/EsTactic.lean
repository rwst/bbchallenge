/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Inspired by BusyCoq's `es` tactic (Individual62.v).
-/
import BusyLean.Defs
import BusyLean.RunLemmas
import BusyLean.TapeHelpers
import BusyLean.Notation
import BusyLean.Multistep
import Lean.Elab.Tactic

/-!
# BusyLean: `es` tactic (symbolic evaluator)

A BusyCoq-style symbolic evaluator for TM proofs. Operates on `EvStep` goals
(`A -[tm]->* B`) and alternates between:
1. **Concrete stepping**: take TM steps while state/head are concrete
2. **Shift rule application**: when stuck on a variable-length block,
   apply a user-provided shift lemma

## Usage

```lean
theorem foo : S1 a b c -[tm]->* S2 a' b' c' := by
  es tm [shift_lemma_1, shift_lemma_2, ...]
```

The shift lemmas should be `EvStep` proofs (or `run` equalities) of the form:
```lean
theorem my_shift (k : Nat) (L R : List Sym) :
    config_with_block_k -[tm]->* config_without_block
```
-/

namespace BusyLean

open Lean Elab Tactic Meta

/-! ### Helpers -/

/-- Parse `EvStep tm A B` from an expression. -/
private def parseEvStep' (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``EvStep 4 then
    some (e.getArg! 1, e.getArg! 2, e.getArg! 3)
  else none

/-- Check if expr is a concrete `some (Fin.mk n _)` (i.e., a known TM state). -/
private def isConcreteState (e : Expr) : Bool :=
  -- Match: Option.some (Fin.mk n _) where n is a literal
  if e.isAppOfArity ``Option.some 2 then
    let inner := e.getArg! 1
    if inner.isAppOfArity ``Fin.mk 3 then
      match inner.getArg! 1 with
      | .lit (.natVal _) => true
      | _ => false
    else false
  else false

/-- Check if expr is a concrete `true` or `false`. -/
private def isConcreteBool (e : Expr) : Bool :=
  e.isConstOf ``Bool.true || e.isConstOf ``Bool.false

/-- Extract the 4 fields of a Config struct: (state, left, head, right).
    Uses `whnf` for efficiency instead of full `reduce`. -/
private def extractConfigFields (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  try
    let st ← whnf (← mkAppM ``Config.state #[e])
    let l ← whnf (← mkAppM ``Config.left #[e])
    let h ← whnf (← mkAppM ``Config.head #[e])
    let r ← whnf (← mkAppM ``Config.right #[e])
    return some (st, l, h, r)
  catch _ => return none

/-! ### Core: take one concrete TM step -/

/-- `es_step1` — take one TM step on an `A -[tm]->* B` goal.

    Computes `step tm A` when A has concrete state and head.
    Transforms goal from `A -[tm]->* B` to `step(A) -[tm]->* B`. -/
private def esStep1 (tmExpr : Expr) (tmId : Ident) : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then return false
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, srcExpr, _) := parseEvStep' goalType
    | return false
  -- Compute the step result via kernel isDefEq: build the expected config structure
  -- and check if `run tm src 1` is defeq to it. Use `change` which invokes the kernel.
  let saved ← saveState
  try
    -- Apply the step. Use first/try to handle the case where this closes the goal.
    evalTactic (← `(tactic| first | (exact EvStep.trans ⟨1, rfl⟩ EvStep.refl)
                                    | (refine EvStep.trans ⟨1, rfl⟩ ?_)))
    -- Check if the goal was completely solved
    let remainingGoals ← getGoals
    if remainingGoals.isEmpty then return true
    let newGoal ← getMainGoal
    let newGoalType ← newGoal.getType
    let some (tmE, runSrc, tgt) := parseEvStep' newGoalType
      | saved.restore; return false
    -- Use isDefEq to check if runSrc reduces to a Config.mk application
    let runSrcWhnf ← withTransparency .all (whnf runSrc)
    -- Check: is it a struct constructor application?
    let headFn := runSrcWhnf.getAppFn
    unless headFn.isConstOf ``Config.mk do
      saved.restore; return false
    -- It reduced! Now change the goal to use the reduced form.
    let newEvStep ← mkAppM ``EvStep #[tmE, runSrcWhnf, tgt]
    let _ ← newGoal.change newEvStep
    return true
  catch _ =>
    saved.restore
    return false

/-! ### Core: try to close the goal -/

/-- `es_finish` — try to close `A -[tm]->* B` when A ≈ B. -/
private def esFinish : TacticM Bool := do
  let goals ← getGoals
  if goals.isEmpty then return true
  let saved ← saveState
  try
    evalTactic (← `(tactic| exact EvStep.refl))
    return true
  catch _ =>
    saved.restore
  try
    evalTactic (← `(tactic|
      (refine ⟨0, ?_⟩; simp only [Multistep, run_zero]
       first | rfl | (congr 1 <;> (first | rfl | omega | (congr 1 <;> omega)))
             | (simp only [ones_append, zeros_append, zebra_append,
                            List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
                congr 1 <;> (first | rfl | omega | (congr 1 <;> omega))))))
    return true
  catch _ =>
    saved.restore
    return false

/-! ### Core: apply a shift rule -/

/-- `es_try_shift` — try to apply a single shift lemma.

    The shift lemma should be an EvStep or run-equality.
    We apply it via `evstep_follow`-style: `EvStep.trans shift ?_`. -/
private def esTryShift (shiftExpr : Expr) : TacticM Bool := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, goalA, _) := parseEvStep' goalType
    | return false
  -- Elaborate and lift to EvStep
  let shiftType ← inferType shiftExpr
  let shiftType := shiftType.consumeMData
  let evShift ←
    if let some (_, hA, _) := parseEvStep' shiftType then
      unless ← isDefEq goalA hA do return false
      pure shiftExpr
    else if shiftType.isAppOfArity ``Eq 3 then
      -- run equality: lift via EvStep.from_multistep
      let lifted ← mkAppM ``EvStep.from_multistep #[shiftExpr]
      let liftedType ← inferType lifted
      let some (_, hA, _) := parseEvStep' liftedType
        | return false
      unless ← isDefEq goalA hA do return false
      pure lifted
    else
      return false
  -- Apply: refine EvStep.trans evShift ?_
  let saved ← saveState
  try
    let hSyn ← Term.exprToSyntax evShift
    evalTactic (← `(tactic| refine EvStep.trans $hSyn ?_))
    return true
  catch _ =>
    saved.restore
    return false

/-! ### Main tactic -/

/-- `es` — BusyCoq-style symbolic evaluator for EvStep goals.

    Usage: `es tm_def [shift1, shift2, ...]`

    Alternates between concrete TM steps and shift rule applications
    until the goal is closed or no progress can be made.

    Example:
    ```lean
    theorem LOv1 : S1 0 b (3+c) -[tm]->* S1 (2+b) 2 c := by
      simp only [S1]
      es tm [zebra_traverse, cd_pair_retreat, BEDA_traverse, ...]
    ```
-/
syntax "es " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| es $tmId [ $shifts,* ]) => do
    -- Resolve TM expression
    let tmExpr ← Term.elabTerm tmId none
    -- Elaborate shift lemmas
    let shiftExprs ← shifts.getElems.toList.mapM fun (s : TSyntax `term) =>
      Term.elabTerm s.raw none
    -- Main loop
    let maxIter := 500
    for _ in List.range maxIter do
      -- Check if there are any goals left
      let goals ← getGoals
      if goals.isEmpty then return
      -- Try to finish
      if ← esFinish then return
      -- Try concrete steps (take up to 20 at a time before checking shifts)
      let mut stepped := false
      for _ in List.range 20 do
        let gs ← getGoals
        if gs.isEmpty then return
        if ← esStep1 tmExpr tmId then
          stepped := true
        else
          break
      -- Try to finish after stepping
      if ← esFinish then return
      -- If we stepped, loop again
      if stepped then continue
      -- Try shift rules
      let mut shifted := false
      for shiftExpr in shiftExprs do
        if ← esTryShift shiftExpr then
          shifted := true
          break
      if shifted then continue
      -- Stuck: no steps and no shifts worked
      let goal ← getMainGoal
      let goalType ← goal.getType
      let goalFmt ← ppExpr goalType
      throwError m!"es: stuck — no concrete steps or shift rules apply\nGoal: {goalFmt}"
    throwError "es: exceeded maximum iterations ({maxIter})"

end BusyLean
