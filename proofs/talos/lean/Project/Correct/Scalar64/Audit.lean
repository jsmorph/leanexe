import Lean
import Project.Correct.Scalar64.Artifacts
import Project.Correct.Scalar64.ValidationTests

/-! This gate rejects any nonstandard transitive axiom in every public
correctness declaration, and retains the independent TypeSafety policy. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut scalarCount : Nat := 0
  let mut independentCount : Nat := 0
  for (name, _) in env.constants.toList do
    let independent := `LeanExe.TypeSafety |>.isPrefixOf name
    let scalar := (`LeanExe.Correct.Scalar64).isPrefixOf name ||
      (`Project.Correct.Scalar64).isPrefixOf name
    if independent || scalar then
      let allowed := if independent then #[`propext]
        else #[`propext, `Classical.choice, `Quot.sound]
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "unapproved axiom {axiomName} in {name}"
      if independent then independentCount := independentCount + 1
      else scalarCount := scalarCount + 1
  logInfo m!"audited {scalarCount} scalar and {independentCount} independent declarations"
