import Verified.Examples.WasiDepth
import Verified.Examples.WasiRetainTotal

open Lean Elab Command in
elab "check_wasi_acceptance_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Examples.WasiDepth.compiled.effectHelper.implements,
    ``Verified.Examples.WasiDepth.compiled.effectHelper.total,
    ``Verified.Examples.WasiDepth.compiled.effectCaller.implements,
    ``Verified.Examples.WasiDepth.compiled.effectCaller.total,
    ``Verified.Examples.WasiDepth.compiled.encoded,
    ``Verified.Examples.WasiDepth.compiled.decoded,
    ``Verified.Examples.WasiRetain.source_body,
    ``Verified.Examples.WasiRetain.body_prefix_bound,
    ``Verified.Examples.WasiRetain.call_prefix_bound,
    ``Verified.Examples.WasiRetain.initial_within,
    ``Verified.Examples.WasiRetain.retain_total,
    ``Verified.Examples.WasiRetain.compiled.encoded,
    ``Verified.Examples.WasiRetain.compiled.decoded]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI acceptance axiom check passed for {theorems.size} theorems"

check_wasi_acceptance_axioms
