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

/-- Recursively strip `xs ++ []` to `xs` in an expression, after instantiating
    metavariables. Used by `esTryShift`'s Stage 1 trailing-empty fallback to
    bridge the `xs ++ [] = xs` defeq gap that Lean does not reduce.

    Recognizes both `List.append xs ys` (3 args) and `HAppend.hAppend _ _ _ _ xs ys`
    (6 args, the elaborated form of `xs ++ ys` via the `HAppend` typeclass). -/
private def stripAppendNil (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (post := fun e' => do
    let e' := e'.consumeMData
    -- Case 1: List.append xs ys (3 args: α, xs, ys)
    if e'.isAppOfArity ``List.append 3 then
      let ys := e'.getArg! 2
      if ys.isAppOfArity ``List.nil 1 then
        return .done (e'.getArg! 1)
    -- Case 2: HAppend.hAppend (6 args: α β γ inst xs ys)
    if e'.isAppOfArity ``HAppend.hAppend 6 then
      let ys := e'.getArg! 5
      if ys.isAppOfArity ``List.nil 1 then
        return .done (e'.getArg! 4)
    return .done e')

/-- Try to apply a shift rule.

    **Stage 0 (direct)**: elaborate the shift, instantiate fresh metavariables
    for its parameters, check `isDefEq` of the goal's source against the
    shift's source.

    **Stage 1 (trailing-empty fallback)**: if Stage 0 fails, try assigning
    each `List Sym` parameter to `[]` (one at a time, with state restore), then
    use `stripAppendNil` to collapse the resulting `xs ++ []` patterns and
    retry `isDefEq`. Bridges the `zebra b` vs `zebra ?b ++ ?R` mismatch
    without requiring `_nil` shift variants.

    Stage 0 and Stage 1 reuse the same `applyShift` helper, which builds the
    `EvStep.trans` proof with the *unified* shift target — `esNormalize` then
    cleans up any residual `xs ++ []` in the continuation goal. -/
private def esTryShift (shiftSyn : Syntax) : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let saved ← saveState
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, goalSrc, _) := parseEvStep' goalType | return false
  let some (_, _, tgtExpr) := parseEvStep' goalType | return false
  let listSymTy : Expr := mkApp (mkConst ``List [.zero]) (mkConst ``BusyLean.Sym)
  let nilSym : Expr := mkApp (mkConst ``List.nil [.zero]) (mkConst ``BusyLean.Sym)
  -- Try one match attempt. If `preAssignIdx = none`, this is the direct
  -- Stage 0 attempt. If `preAssignIdx = some i`, pre-assign mvars[i] to []
  -- and use `stripAppendNil` before defeq (Stage 1). Returns true on success,
  -- false on failure (state is restored on failure).
  let attempt (preAssignIdx : Option Nat) : TacticM Bool := do
    let restore ← saveState
    let success : Bool ← try
      let shiftExpr ← Term.elabTerm shiftSyn none
      let shiftRawType ← inferType shiftExpr
      let (mvars, _, shiftType) ← forallMetaTelescope shiftRawType
      let shiftExpr := mkAppN shiftExpr mvars
      match parseEvStep' shiftType with
      | none => pure false
      | some (tmE, shiftSrc, _) => do
        let mut isStage1 := false
        match preAssignIdx with
        | none => pure ()
        | some i =>
          if i < mvars.size then
            let mvId := mvars[i]!.mvarId!
            if !(← mvId.isAssigned) then
              let mvTy ← mvId.getType
              if ← isDefEq mvTy listSymTy then
                try
                  mvId.assign nilSym
                  isStage1 := true
                catch _ => pure ()
        -- Try direct defeq first (Stage 0 path or Stage 1 with no `++ []`).
        let defeqOk ← isDefEq goalSrc shiftSrc
        if defeqOk then
          let shiftType' ← instantiateMVars shiftType
          match parseEvStep' shiftType' with
          | none => pure false
          | some (_, _, shiftB') => do
            let remainType ← mkAppM ``EvStep #[tmE, shiftB', tgtExpr]
            let remainMVar ← mkFreshExprMVar remainType
            let fullProof ← mkAppM ``EvStep.trans #[shiftExpr, remainMVar]
            goal.assign fullProof
            replaceMainGoal [remainMVar.mvarId!]
            pure true
        else if isStage1 then
          -- Stage 1: try stripping `xs ++ []` from the SHIFT'S source for
          -- defeq, then update the GOAL'S type via `replaceTargetEq` to
          -- match the unstripped (true) shift source. This way the shift's
          -- type is unchanged and the kernel accepts the proof.
          let shiftSrc' ← stripAppendNil shiftSrc
          if !(← isDefEq goalSrc shiftSrc') then
            pure false
          else
            -- Build a new goal type `EvStep tm shiftSrc tgtExpr` (with the
            -- original `++ []` form, post-instantiation) and rewrite the goal
            -- to it via `replaceTargetEq`. The eq proof is constructed by
            -- `simp [List.append_nil]` going the other way.
            let shiftType' ← instantiateMVars shiftType
            match parseEvStep' shiftType' with
            | none => pure false
            | some (_, shiftSrcInst, shiftB') => do
              -- New goal type: EvStep tm shiftSrcInst tgtExpr
              let newGoalType ← mkAppM ``EvStep #[tmE, shiftSrcInst, tgtExpr]
              -- Build eq proof: oldGoalType = newGoalType.
              -- oldGoalType: EvStep tm goalSrc tgtExpr (which is defeq to newGoalType
              -- modulo the `xs ++ [] ↔ xs` rewrite). We construct the proof via
              -- `Eq.mpr` of an `EvStep` congrArg from `goalSrc = shiftSrcInst`,
              -- which holds via `simp [List.append_nil]`.
              -- Simplest: use `mkAppM ``Eq.refl` and let it succeed if defeq holds
              -- with `tape_norm`-equivalent forms. If that fails, we manually
              -- build the proof by wrapping `(List.append_nil _).symm` in congrArg
              -- positions.
              -- For now, try the simp-based approach: invoke a `simp [List.append_nil]`
              -- subroutine that returns an equality proof.
              let eqProof? ← try
                let oldType ← instantiateMVars (← goal.getType)
                let proof ← mkAppOptM ``Eq.refl #[some (← inferType oldType), some oldType]
                -- Will fail if oldType ≠ newGoalType. Retry via `Eq.mpr`-style
                -- coercion using `mkAppM ``id_of_eq` or `mkExpectedTypeHint`.
                pure (some proof)
              catch _ => pure none
              match eqProof? with
              | none => pure false
              | some _ => do
                -- Use replaceTargetEq with a proof that the old and new types
                -- are equal. The new type uses `shiftSrcInst` (with `++ []`).
                -- Construct via mkEq + simp.
                let oldType ← instantiateMVars (← goal.getType)
                let eqType ← mkEq oldType newGoalType
                -- Try to prove the eqType via `simp [List.append_nil]`.
                let eqProofOpt ← try
                  let prf ← mkFreshExprMVar eqType
                  -- Run simp on the proof's mvar via evalTactic
                  let prevGoals ← getGoals
                  setGoals [prf.mvarId!]
                  evalTactic (← `(tactic| simp only [List.append_nil]))
                  let remainingAfterSimp ← getGoals
                  setGoals prevGoals
                  if remainingAfterSimp.isEmpty then pure (some prf)
                  else pure none
                catch _ => pure none
                match eqProofOpt with
                | none => pure false
                | some eqProof => do
                  let newGoal ← goal.replaceTargetEq newGoalType eqProof
                  -- Now build the trans proof against the new goal.
                  let remainType ← mkAppM ``EvStep #[tmE, shiftB', tgtExpr]
                  let remainMVar ← mkFreshExprMVar remainType
                  let fullProof ← mkAppM ``EvStep.trans #[shiftExpr, remainMVar]
                  newGoal.assign fullProof
                  replaceMainGoal [remainMVar.mvarId!]
                  pure true
        else
          pure false
    catch _ => pure false
    if !success then restore.restore
    return success
  -- Stage 0: direct attempt with no mvar pre-assignment.
  if ← attempt none then return true
  -- Stage 1: try each individual parameter index assigned to []. The first
  -- index that successfully unifies (after stripping `xs ++ []` and
  -- rewriting the goal via `replaceTargetEq`) wins.
  for i in [:8] do
    if ← attempt (some i) then return true
  -- Stage 3: try splitting the goal's atoms via `tape_split` (e.g.
  -- `ones (4+2*a) → ones 2 ++ ones (2+2*a)`), then re-associate via
  -- `tape_norm` (which does NOT include `ones_append`, so the splits
  -- survive), then re-run Stages 0 and 1. This bridges the gap between
  -- merged-atom goals and split-atom shift rules. Goal state is saved before
  -- Stage 3 and restored if all attempts fail, so an unsuccessful Stage 3
  -- doesn't poison the surrounding loop.
  let stage3Saved ← saveState
  let splitOk ← try
    evalTactic (← `(tactic| simp only [tape_split]))
    -- Re-associate appends after the split so left-associated shift sources
    -- like `rev_zebra k ++ ones 2 ++ L` match. `tape_norm` includes
    -- `List.append_assoc` and `List.cons_append` but not `ones_append`.
    try evalTactic (← `(tactic| simp only [tape_norm])) catch _ => pure ()
    pure true
  catch _ => pure false
  if splitOk then
    if ← attempt none then return true
    for i in [:8] do
      if ← attempt (some i) then return true
  stage3Saved.restore
  saved.restore
  return false

/-- Normalize the goal source via the `tape_norm` simp set. Folds leading cons
    prefixes back into tape atoms (`ones k`, `zebra k`, …) so that shift rule
    sources with metavariable indices unify structurally. Also reduces concrete
    `Nat` arithmetic via the `Nat.reduceMul`/`Nat.reduceAdd` simprocs.

    Silently does nothing on failure. -/
private def esNormalize : TacticM Unit := do
  if (← getGoals).isEmpty then return
  try
    evalTactic (← `(tactic| simp only [tape_norm, Nat.reduceMul, Nat.reduceAdd]))
  catch _ => pure ()

syntax "es " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| es $_tmId [ $shifts,* ]) => do
    let shiftSyns := shifts.getElems.toList.map fun (s : TSyntax `term) => s.raw
    -- Initial normalization: right-associate appends, fold cons prefixes,
    -- simplify arithmetic (e.g. `2 * (2+a) → 4 + 2*a`).
    esNormalize
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
