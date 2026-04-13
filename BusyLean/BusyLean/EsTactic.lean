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

/-! # BusyLean: `es` tactic (symbolic evaluator)

Batch-stepping symbolic evaluator: takes concrete TM steps via `whnf` in MetaM
(no evalTactic per step), applies shift rules when stuck, closes with `esFinish`.
-/

namespace BusyLean

open Lean Elab Tactic Meta

private def parseEvStep' (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``EvStep 4 then some (e.getArg! 1, e.getArg! 2, e.getArg! 3)
  else none

private def esFinish : TacticM Bool := do
  if (← getGoals).isEmpty then return true
  let saved ← saveState
  -- First try: exact EvStep.refl (syntactic equality)
  let ok ← try evalTactic (← `(tactic| exact EvStep.refl)); pure true
           catch _ => saved.restore; pure false
  if ok then return true
  -- Second try: 0-step proof with normalization
  let saved2 ← saveState
  let ok2 ← try
    evalTactic (← `(tactic|
      (refine ⟨0, ?_⟩
       show _ = _
       simp only [List.append_nil, List.nil_append,
                  List.append_assoc, List.cons_append]
       rfl)))
    pure true
  catch _ => saved2.restore; pure false
  return ok2

/-- Check if an expression is a "concrete head" — i.e., literally `true`, `false`,
    or stuck on a `listHead/listTail` recursor that won't reduce further.
    Returns true if it's a concrete Bool (further stepping is possible). -/
private def isConcreteHead (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isConstOf ``true || e.isConstOf ``false ||
  (e.isAppOfArity ``Bool.true 0) || (e.isAppOfArity ``Bool.false 0)

/-- Take one TM step using `Meta.reduce` to fully reduce `step tm src` to a
    concrete `Config.mk` literal. The reducer handles match/projection reduction
    automatically, producing the next config with state and head computed.

    Strategy:
    1. Build proof `⟨1, rfl⟩ : EvStep tm src (run tm src 1)` in MetaM (Option 3).
    2. Use `Meta.reduce` to compute `cur := step tm src`. This produces a
       `Config.mk` literal where state and (when computable) head are concrete.
    3. Build new goal `EvStep tm cur tgt`. The kernel checks `run tm src 1 ≡ cur`
       once when verifying the final proof — much cheaper than per-step defeq.
    4. Returns false if `cur` doesn't have a concrete head (further steps would
       require reading from a variable tape — caller should try shifts). -/
private def esStep1 : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (tmE, srcE, tgtE) := parseEvStep' goalType | return false
  let goalTypeC := goalType.consumeMData
  let nE := goalTypeC.getArg! 0
  let saved ← saveState
  try
    -- Compute `step tm src` via Meta.reduce
    let stepApp := mkAppN (mkConst ``step) #[nE, tmE, srcE]
    let cur ← Meta.reduce stepApp (skipProofs := true) (skipTypes := true)
    -- Sanity: result should be a Config.mk-shaped expression
    unless cur.isAppOf ``Config.mk do
      saved.restore
      return false
    -- Check: is the new head concrete? If not, further stepping won't progress.
    -- Config.mk has 5 args: {n} state left head right
    let headArg := cur.getArg! 3
    unless isConcreteHead headArg do
      saved.restore
      return false
    -- Build proof: ⟨1, rfl⟩ : EvStep tm src cur
    -- where rfl : run tm src 1 = cur (kernel checks defeq once)
    let oneE := mkNatLit 1
    let runExpr := mkAppN (mkConst ``run) #[nE, tmE, srcE, oneE]
    let configType := mkApp (mkConst ``Config []) nE
    -- The rfl here has type `run tm src 1 = run tm src 1`, but is used as
    -- `run tm src 1 = cur` — kernel verifies via defeq when checking the proof.
    let rflExpr := mkApp2 (mkConst ``Eq.refl [1]) configType runExpr
    let stepPf ← mkAppOptM ``EvStep.from_multistep
      #[some nE, some tmE, some srcE, some cur, some oneE, some rflExpr]
    -- New goal: EvStep tm cur tgt
    let newGoalType := mkAppN (mkConst ``EvStep) #[nE, tmE, cur, tgtE]
    let newMVar ← mkFreshExprMVar newGoalType
    let fullProof := mkAppN (mkConst ``EvStep.trans)
      #[nE, tmE, srcE, cur, tgtE, stepPf, newMVar]
    goal.assign fullProof
    replaceMainGoal [newMVar.mvarId!]
    return true
  catch _ =>
    saved.restore
    return false

/-- Take up to `n` concrete TM steps without checking shifts/finish. -/
private def esStepN (maxSteps : Nat) : TacticM Nat := do
  let mut count := 0
  for _ in [:maxSteps] do
    if (← getGoals).isEmpty then return count
    if ← esStep1 then count := count + 1
    else return count
  return count

/-- Try to apply a shift rule. Elaborates the shift, instantiates with fresh
    metavariables for its arguments, and checks defeq against the goal source. -/
private def esTryShift (shiftSyn : Syntax) : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let saved ← saveState
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, goalSrc, _) := parseEvStep' goalType | return false
  let some (_, _, tgtExpr) := parseEvStep' goalType | return false
  try
    let shiftExpr ← Term.elabTerm shiftSyn none
    let shiftRawType ← inferType shiftExpr
    -- Apply to fresh metavariables for any remaining Pi binders so that
    -- the result has type EvStep tm A B (not ∀ ..., EvStep ...).
    let (mvars, _, shiftType) ← forallMetaTelescope shiftRawType
    let shiftExpr := mkAppN shiftExpr mvars
    let some (tmE, shiftSrc, shiftB) := parseEvStep' shiftType | do
      saved.restore; return false
    -- Check defeq
    unless (← isDefEq goalSrc shiftSrc) do
      saved.restore
      return false
    -- Apply: build EvStep.trans shiftExpr ?rest
    let remainType ← mkAppM ``EvStep #[tmE, shiftB, tgtExpr]
    let remainMVar ← mkFreshExprMVar remainType
    let fullProof ← mkAppM ``EvStep.trans #[shiftExpr, remainMVar]
    goal.assign fullProof
    replaceMainGoal [remainMVar.mvarId!]
    return true
  catch _ =>
    saved.restore
    return false

/-- Normalize the goal source via simp to canonicalize tape associativity,
    `[]`-appends, and split `List.replicate` of a sum into prepended `List.replicate 2`.
    Silently does nothing on failure. -/
private def esNormalize : TacticM Unit := do
  if (← getGoals).isEmpty then return
  try
    evalTactic (← `(tactic|
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
                 ← BusyLean.replicate_append,
                 List.append_nil, List.nil_append, List.cons_append]))
  catch _ => pure ()

syntax "es " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| es $tmId [ $shifts,* ]) => do
    let shiftSyns := shifts.getElems.toList.map fun (s : TSyntax `term) => s.raw
    for _ in [:200] do
      if (← getGoals).isEmpty then return
      if ← esFinish then return
      -- Try shift rules FIRST: they reduce many steps in one defeq check,
      -- avoiding the per-step cost of esStep1 entirely when applicable.
      let mut shifted := false
      for shiftSyn in shiftSyns do
        if (← getGoals).isEmpty then return
        let shOk ← try pure (← esTryShift shiftSyn) catch _ => pure false
        if shOk then shifted := true; break
      if (← getGoals).isEmpty then return
      if shifted then
        esNormalize
        continue
      -- No shift applied — take concrete steps to reach the next shift point.
      let stepped ← esStepN 30
      if (← getGoals).isEmpty then return
      if ← esFinish then return
      if stepped > 0 then
        esNormalize
        continue
      let goal ← getMainGoal
      let goalFmt ← ppExpr (← goal.getType)
      throwError m!"es: stuck\nGoal: {goalFmt}"
    if (← getGoals).isEmpty then return
    let goal ← getMainGoal
    let goalFmt ← ppExpr (← goal.getType)
    throwError m!"es: exceeded maximum iterations\nGoal: {goalFmt}"

end BusyLean
