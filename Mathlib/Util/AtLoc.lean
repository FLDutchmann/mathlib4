/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.Simp.Main

/-!
# `ring_nf` tactic

A tactic which uses `ring` to rewrite expressions. This can be used non-terminally to normalize
ring expressions in the goal such as `⊢ P (x + x + x)` ~> `⊢ P (x * 3)`, as well as being able to
prove some equations that `ring` cannot because they involve ring reasoning inside a subterm,
such as `sin (x + y) + sin (y + x) = 2 * sin (x + y)`.

-/

namespace Mathlib.Tactic
open Lean Meta

open Elab.Tactic
variable (m : (e : Expr) → MetaM Simp.Result)

/-- Use the procedure `m` to rewrite the main goal. -/
def atTarget (proc : String) (failIfUnchanged : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← m tgt
  if r.expr.consumeMData.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    let newGoal ← applySimpResultToTarget goal tgt r
    if failIfUnchanged && goal == newGoal then
      throwError "{proc} made no progress"
    replaceMainGoal [newGoal]

/-- Use the procedure `m` to rewrite hypothesis `h`. -/
def atLocalDecl (proc : String) (failIfUnchanged : Bool) (mayCloseGoal : Bool) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← m tgt
  match ← applySimpResultToLocalDecl goal fvarId myres mayCloseGoal with
  | none => replaceMainGoal []
  | some (_, newGoal) =>
    if failIfUnchanged && goal == newGoal then
      throwError "{proc} made no progress"
    replaceMainGoal [newGoal]

/-- Use the procedure `m` to rewrite at specified locations. -/
def atLoc (proc : String) (failIfUnchanged : Bool) (mayCloseGoalFromHyp : Bool) (loc : Location) :
    TacticM Unit :=
  Lean.Elab.Tactic.withLocation loc (atLocalDecl m proc failIfUnchanged mayCloseGoalFromHyp)
    (atTarget m proc failIfUnchanged)
    fun _ ↦ throwError "{proc} failed"

end Mathlib.Tactic
