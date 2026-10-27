import Verified.Wasi.CommandBindValueSpec
import Verified.Wasi.CommandCorrect
import Verified.Wasi.CallBudget
import Verified.Wasi.CostCallHelper
import Verified.Wasi.CostCallSpec
import Verified.Wasi.CostCommandCorrect
import Verified.Wasi.Correct
import Verified.Wasi.ProgramInitial

open Lean Elab Command in
elab "check_wasi_compiler_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.command_bind_value_spec,
    ``Verified.Wasi.Command.code_spec,
    ``Verified.Wasi.ArgumentsAfter.call_budget,
    ``Verified.Wasi.call_arguments_allowed,
    ``Verified.Wasi.wp_cost_effect_helper,
    ``Verified.Wasi.cost_command_call_spec,
    ``Verified.Wasi.Command.cost_code_spec,
    ``Verified.Wasi.EffectProg.correct,
    ``Verified.Wasi.EffectProg.correctWith,
    ``Verified.Wasi.compileWith_initialStore]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI compiler axiom check passed for {theorems.size} theorems"

check_wasi_compiler_axioms
