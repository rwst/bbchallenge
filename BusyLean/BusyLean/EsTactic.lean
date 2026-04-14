/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import BusyLean.Defs
import BusyLean.RunLemmas
import BusyLean.TapeHelpers
import BusyLean.TapeNorm
import BusyLean.Notation
import BusyLean.Multistep
import BusyLean.Nonhalt
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
  -- Fast path 1: EvStep.refl (syntactic equality)
  let ok ← try evalTactic (← `(tactic| exact EvStep.refl)); pure true
           catch _ => saved.restore; pure false
  if ok then return true
  -- Fast path 2: 0-step with tape_norm + rfl (handles cons-fold)
  let saved2 ← saveState
  let ok2 ← try
    evalTactic (← `(tactic|
      (refine ⟨0, ?_⟩
       unfold Multistep run
       try simp only [tape_norm, List.append_nil, List.nil_append,
                      List.append_assoc, List.cons_append]
       rfl)))
    pure true
  catch _ => saved2.restore; pure false
  if ok2 then return true
  -- Fast path 3: 0-step + field-wise congr with omega for Nat index equalities.
  -- `unfold Multistep run` reduces `run tm A 0 = B` to `A = B`, enabling `congr 1`.
  -- The cascade handles up to four nested levels: Config → List → atom → Nat.
  let saved3 ← saveState
  let ok3 ← try
    evalTactic (← `(tactic|
      (refine ⟨0, ?_⟩
       unfold Multistep run
       try simp only [tape_norm, List.append_nil, List.nil_append,
                      List.append_assoc, List.cons_append]
       first
         | rfl
         | (congr 1 <;>
            first | rfl | omega
                  | (congr 1 <;>
                     first | rfl | omega
                           | (congr 1 <;>
                              first | rfl | omega
                                    | (congr 1 <;> first | rfl | omega)))))))
    pure true
  catch _ => saved3.restore; pure false
  return ok3

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

/-- Normalize the goal source via the `tape_norm` simp set. Folds leading cons
    prefixes back into tape atoms (`ones k`, `zebra k`, …) so that shift rule
    sources with metavariable indices unify structurally.

    Silently does nothing on failure. -/
private def esNormalize : TacticM Unit := do
  if (← getGoals).isEmpty then return
  try
    evalTactic (← `(tactic| simp only [tape_norm]))
  catch _ => pure ()

syntax "es " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| es $_tmId [ $shifts,* ]) => do
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

/-! ### `esx` — halts-goal variant

`esx tm [shifts]` proves goals of the form `∃ k, (run tm A k).halted`. It
reduces the goal to an `EvStep` via `halts_of_evstep_halted`, then runs an
es-like loop until the current source has `state := none`. At that point the
final config is a concrete halted `Config.mk` literal; we close the EvStep
subgoal via `EvStep.refl` (unifying the metavariable target) and the
`.halted` subgoal via `rfl`. -/

/-- Check whether a reduced `Config.mk` expression has `state := none`. -/
private def isHaltedConfig (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOf ``Config.mk then
    let args := e.getAppArgs
    -- Args: {n}, state, left, head, right — state is at index 1.
    if h : args.size ≥ 2 then
      (args[1]'(by omega)).consumeMData.isAppOf ``Option.none
    else false
  else false

/-- Check if the current EvStep goal has a halted source. If so, close with
    `EvStep.refl` (which unifies the target metavariable). -/
private def esxTryHalt : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, srcE, _) := parseEvStep' goalType | return false
  -- Reduce the source so match/projection are computed
  let srcE' ← try Meta.reduce srcE (skipProofs := true) (skipTypes := true)
               catch _ => pure srcE
  if isHaltedConfig srcE' then
    let saved ← saveState
    try
      evalTactic (← `(tactic| exact EvStep.refl))
      return true
    catch _ =>
      saved.restore
      return false
  else
    return false

syntax "esx " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| esx $_tmId [ $shifts,* ]) => do
    let shiftSyns := shifts.getElems.toList.map fun (s : TSyntax `term) => s.raw
    -- Step 1: convert `∃ k, (run tm A k).halted` via `halts_of_evstep_halted`.
    -- This introduces a metavariable `?c` for the intermediate config and
    -- splits the goal into (a) `A -[tm]->* ?c` and (b) `?c.halted`.
    evalTactic (← `(tactic| apply halts_of_evstep_halted))
    -- Initial normalization: right-associate appends, fold cons prefixes.
    esNormalize
    -- First goal: EvStep loop until source is halted.
    for _ in [:200] do
      if (← getGoals).isEmpty then break
      -- Check halt first: if source is halted, close via EvStep.refl.
      if ← esxTryHalt then break
      -- Try shifts.
      let mut shifted := false
      for shiftSyn in shiftSyns do
        if (← getGoals).isEmpty then break
        let shOk ← try pure (← esTryShift shiftSyn) catch _ => pure false
        if shOk then shifted := true; break
      if (← getGoals).isEmpty then break
      if shifted then
        esNormalize
        continue
      -- Take concrete steps.
      let stepped ← esStepN 30
      if (← getGoals).isEmpty then break
      if stepped > 0 then
        esNormalize
        continue
      -- Try halt one more time before giving up (stepping may have reached
      -- a halted state in a mid-batch).
      if ← esxTryHalt then break
      let goal ← getMainGoal
      let goalFmt ← ppExpr (← goal.getType)
      throwError m!"esx: stuck (no shifts/steps applicable and source not halted)\nGoal: {goalFmt}"
    -- Second goal: `?c.halted` — now `?c` has been unified with a concrete
    -- halted Config.mk, so it reduces to `none = none`.
    if !(← getGoals).isEmpty then
      try evalTactic (← `(tactic| rfl))
      catch _ =>
        try evalTactic (← `(tactic| decide))
        catch _ =>
          try evalTactic (← `(tactic| simp [Config.halted]))
          catch _ => pure ()
    if !(← getGoals).isEmpty then
      let goal ← getMainGoal
      let goalFmt ← ppExpr (← goal.getType)
      throwError m!"esx: failed to close halted subgoal\nGoal: {goalFmt}"

end BusyLean
