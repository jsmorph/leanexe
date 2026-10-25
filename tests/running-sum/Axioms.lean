import Demos.RunningSum.Compiled

open Lean Elab Command in
elab "check_running_sum_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Demos.RunningSum.arithmetic.zero.implements,
    ``Demos.RunningSum.arithmetic.parse.implements,
    ``Demos.RunningSum.arithmetic.magnitudeLess.implements,
    ``Demos.RunningSum.arithmetic.combineMagnitude.implements,
    ``Demos.RunningSum.arithmetic.add.implements,
    ``Demos.RunningSum.arithmetic.render.implements,
    ``Demos.RunningSum.arithmetic.initial,
    ``Demos.RunningSum.arithmetic.bytes]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Running sum axiom check passed for {declarations.size} theorems"

check_running_sum_axioms
