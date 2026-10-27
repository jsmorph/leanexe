import Verified.Examples.TypedTrees

/-! Every theorem of the example of trees whose records hold typed fields uses only the axioms
`propext`, `Classical.choice`, and `Quot.sound`: the theorems that `verified_compile` adds under
`compiled`, and the laws, encodings, and match lemmas that it derives for the recursive types. -/

open Lean Elab Command in
elab "check_typed_tree_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let pre := `Verified.Examples.TypedTrees
  let theorems := (← getEnv).constants.fold (init := #[]) fun acc name info =>
    if pre.isPrefixOf name && info matches .thmInfo _ then acc.push name else acc
  if theorems.size < 150 then
    throwError "found only {theorems.size} theorems under {pre}"
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"typed tree axiom check passed for {theorems.size} theorems"

check_typed_tree_axioms
