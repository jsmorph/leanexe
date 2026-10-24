import Verified.Wasi.CostLoopSpec

open Lean Elab Command in
elab "check_loop_cost_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Resource.ResourceLoopHead.remaining_index,
    ``Verified.Wasi.Resource.ResourceLoopHead.complete,
    ``Verified.Wasi.Resource.ResourceLoopHead.transportPrefix,
    ``Verified.Wasi.Resource.ResourceLoopHead.resources,
    ``Verified.Wasi.Resource.ResourceLoopHead.residualBound,
    ``Verified.Wasi.LoopCostFrame.resources,
    ``Verified.Wasi.LoopCostFrame.test_resources,
    ``Verified.Wasi.LoopCostFrame.tested,
    ``Verified.Wasi.LoopCostReady.body_resources,
    ``Verified.Wasi.LoopCostReady.advance,
    ``Verified.Wasi.LoopCostReady.complete_stop,
    ``Verified.Wasi.LoopCostFrame.complete_done,
    ``Verified.Wasi.Resource.PureContext.loopTestReturnCost,
    ``Verified.Wasi.Resource.PureContext.loopPrepareCost,
    ``Verified.Wasi.Resource.PureContext.loopTestFits_code,
    ``Verified.Wasi.wp_loopTestGuarded,
    ``Verified.Wasi.wp_loopPrepareGuarded,
    ``Verified.Wasi.wp_loopBodyCost,
    ``Verified.Wasi.wp_loopFinishCost,
    ``Verified.Wasi.wp_loopPreparedCost,
    ``Verified.Wasi.cost_command_loop_spec]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Loop cost axiom check passed for {theorems.size} theorems"

check_loop_cost_axioms
