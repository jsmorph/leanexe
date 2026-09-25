import Lean

namespace Project.Compiler

open Lean Meta Elab Tactic

/-- Construct an ordinary reflexivity term and let declaration kernel checking
perform the conversion. This avoids duplicating a large reduction in the
elaborator. It adds no axiom and uses no native-evaluation oracle. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``Eq 3 do
    throwError "kernel_rfl requires an equality"
  let proof ← mkEqRefl target.getAppArgs[2]!
  goal.assign proof
  replaceMainGoal []

end Project.Compiler
