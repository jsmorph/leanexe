import Demos.Slew.Optimal
import Demos.Slew.Premise
import Demos.Slew.Bound

/-! The axiom audit of the slew planner, which `tests/verified/run.sh` runs with
`tools/leanrun --timeout 10m lake env lean tests/slew/Axioms.lean` for `--cases slew` and for the
full run.  It fails when a theorem of the slew planner depends on an axiom other than `propext`,
`Classical.choice`, and `Quot.sound`.  The file theorems of `Demos/Slew/File.lean` read the written
module, so the run checks them by elaborating that file again after it writes the module. -/

open Lean Elab Command in
elab "check_slew_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Demos.Slew.Verified.compiled.bytes,
    ``Demos.Slew.Verified.compiled.plan.implements,
    ``Demos.Slew.Verified.compiled.plan.trapFree,
    ``Demos.Slew.Check.edgeOk_sound,
    ``Demos.Slew.Check.attitudeOk_sound,
    ``Demos.Slew.Safety.plan_safe,
    ``Demos.Slew.NanFree.plan_finite,
    ``Demos.Slew.Premise.plan_premise,
    ``Demos.Slew.Cost.edge_cost_le,
    ``Demos.Slew.Optimal.plan_optimal,
    ``Demos.Slew.Bound.plan_bound,
    ``Demos.Slew.Bound.slew_trapFree]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Slew axiom check passed for {declarations.size} theorems"

check_slew_axioms
