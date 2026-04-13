/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.RunLemmas
import BusyLean.TapeHelpers
import BusyLean.Notation
import BusyLean.Multistep
import Lean.Elab.Tactic

/-! # BusyLean: `es` tactic (symbolic evaluator) -/

namespace BusyLean

open Lean Elab Tactic Meta

private def parseEvStep' (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``EvStep 4 then some (e.getArg! 1, e.getArg! 2, e.getArg! 3)
  else none

private def esFinish : TacticM Bool := do
  if (← getGoals).isEmpty then return true
  let saved ← saveState
  let ok ← try evalTactic (← `(tactic| exact EvStep.refl)); pure true
           catch _ => saved.restore; pure false
  if ok then return true
  let ok2 ← try
    evalTactic (← `(tactic|
      (refine ⟨0, ?_⟩; simp only [Multistep, run_zero]
       first | rfl | (congr 1 <;> (first | rfl | omega | (congr 1 <;> omega)))
             | (simp only [ones_append, zeros_append, zebra_append,
                            List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
                congr 1 <;> (first | rfl | omega | (congr 1 <;> omega))))))
    pure true
  catch _ => saved.restore; pure false
  return ok2

/-- Take one TM step: refine + change + dsimp. -/
private def esStep1 (tmId : Ident) : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let saved ← saveState
  let ok ← try
    evalTactic (← `(tactic| refine EvStep.trans ⟨1, rfl⟩ ?_))
    evalTactic (← `(tactic| simp only [run_one]))
    evalTactic (← `(tactic| dsimp only [step, listHead, listTail]))
    pure true
  catch _ => saved.restore; pure false
  return ok

/-- Try to apply a shift rule. Elaborates the shift INSIDE withoutModifyingState
    first to check if it matches, then applies for real only if it does. -/
private def esTryShift (shiftSyn : Syntax) : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let saved ← saveState
  -- First: check if the shift matches (inside withoutModifyingState to avoid metavar leakage)
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, goalSrc, _) := parseEvStep' goalType | return false
  let doesMatch ← withoutModifyingState do
    try
      let shiftExpr ← Term.elabTerm shiftSyn none
      let shiftType ← inferType shiftExpr
      let some (_, shiftSrc, _) := parseEvStep' (shiftType.consumeMData) | return false
      -- Check: does the shift source match the goal source?
      isDefEq goalSrc shiftSrc
    catch _ => return false
  unless doesMatch do return false
  -- Now apply for real (the shift matches)
  let ok ← try
    let shiftExpr ← Term.elabTerm shiftSyn none
    let shiftType ← inferType shiftExpr
    let some (tmE, _, shiftB) := parseEvStep' (shiftType.consumeMData) | pure false
    let some (_, _, tgtExpr) := parseEvStep' goalType | pure false
    let remainType ← mkAppM ``EvStep #[tmE, shiftB, tgtExpr]
    let remainMVar ← mkFreshExprMVar remainType
    let fullProof ← mkAppM ``EvStep.trans #[shiftExpr, remainMVar]
    goal.assign fullProof
    replaceMainGoal [remainMVar.mvarId!]
    pure true
  catch _ => saved.restore; pure false
  return ok

syntax "es " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| es $tmId [ $shifts,* ]) => do
    let shiftSyns := shifts.getElems.toList.map fun (s : TSyntax `term) => s.raw
    for _ in [:500] do
      if (← getGoals).isEmpty then return
      if ← esFinish then return
      if (← getGoals).isEmpty then return
      let stepped ← try pure (← esStep1 tmId) catch _ => pure false
      if (← getGoals).isEmpty then return
      if ← esFinish then return
      if stepped then continue
      let mut shifted := false
      for shiftSyn in shiftSyns do
        if (← getGoals).isEmpty then return
        let shOk ← try pure (← esTryShift shiftSyn) catch _ => pure false
        if shOk then shifted := true; break
      if (← getGoals).isEmpty then return
      if shifted then continue
      let goal ← getMainGoal
      let goalFmt ← ppExpr (← goal.getType)
      throwError m!"es: stuck\nGoal: {goalFmt}"
    if (← getGoals).isEmpty then return
    let goal ← getMainGoal
    let goalFmt ← ppExpr (← goal.getType)
    throwError m!"es: exceeded maximum iterations\nGoal: {goalFmt}"

end BusyLean
