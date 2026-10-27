import Verified.Examples.HeapSums

/-! Every theorem that `verified_compile` adds for the sums that hold heap values uses only the
axioms `propext`, `Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_heap_sum_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let pre := `Verified.Examples.HeapSums.compiled
  let theorems := (← getEnv).constants.fold (init := #[]) fun acc name info =>
    if pre.isPrefixOf name && info matches .thmInfo _ then acc.push name else acc
  if theorems.size < 150 then
    throwError "found only {theorems.size} theorems under {pre}"
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"heap sum axiom check passed for {theorems.size} theorems"

check_heap_sum_axioms
