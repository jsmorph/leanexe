import Verified.Wasi.ResourcePrefixCoverage
import Verified.Wasi.ResourceLoopBudget
import Verified.Wasi.ResourceCompilerCost
import Verified.Wasi.CostLeaves

open Lean Elab Command in
elab "check_wasi_resource_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.Resource.PureContext.returnCost_nil,
    ``Verified.Wasi.Resource.PureContext.readCost_zero,
    ``Verified.Wasi.Resource.PureContext.readCost_overflow,
    ``Verified.Wasi.Resource.ResourceExec.erase,
    ``Verified.Wasi.Resource.ResourceCall.erase,
    ``Verified.Wasi.Resource.ResourceLoopExec.erase,
    ``Verified.Wasi.Resource.ResourcePrefix.erase,
    ``Verified.Wasi.Resource.ResourceCallPrefix.erase,
    ``Verified.Wasi.Resource.ResourceLoopPrefix.erase,
    ``Verified.Wasi.Resource.PrefixBound.ret,
    ``Verified.Wasi.Resource.PrefixBound.read,
    ``Verified.Wasi.Resource.PrefixBound.write,
    ``Verified.Wasi.Resource.PrefixBound.exit,
    ``Verified.Wasi.Resource.PrefixBound.returned,
    ``Verified.Wasi.Resource.PrefixBound.bind_first,
    ``Verified.Wasi.Resource.PrefixBound.bind_next,
    ``Verified.Wasi.Resource.PrefixBound.ite_condition,
    ``Verified.Wasi.Resource.PrefixBound.ite_yes,
    ``Verified.Wasi.Resource.PrefixBound.ite_no,
    ``Verified.Wasi.Resource.CallPrefixBound.entry,
    ``Verified.Wasi.Resource.CallPrefixBound.body,
    ``Verified.Wasi.Resource.CallPrefixBound.there,
    ``Verified.Wasi.Resource.PrefixBound.call_arguments,
    ``Verified.Wasi.Resource.PrefixBound.call_body,
    ``Verified.Wasi.Resource.PrefixBound.loop_count,
    ``Verified.Wasi.Resource.PrefixBound.loop_init,
    ``Verified.Wasi.Resource.PrefixBound.loop_body,
    ``Verified.Wasi.Resource.LoopPrefixBound.returned,
    ``Verified.Wasi.Resource.LoopPrefixBound.test,
    ``Verified.Wasi.Resource.LoopPrefixBound.step,
    ``Verified.Wasi.Resource.LoopPrefixBound.next,
    ``Verified.Wasi.Resource.command_coverage,
    ``Verified.Wasi.Resource.program_calls_covered,
    ``Verified.Wasi.Resource.ResourceExec.ofExec,
    ``Verified.Wasi.Resource.advance_bind_cases,
    ``Verified.Wasi.Resource.exec_of_pure,
    ``Verified.Wasi.Resource.prefix_pure_exec,
    ``Verified.Wasi.Resource.command_advance_coverage,
    ``Verified.Wasi.Resource.program_calls_advance_covered,
    ``Verified.Wasi.Resource.ResourcePrefix.ofAdvance,
    ``Verified.Wasi.Resource.ResourceLoopPrefix.ofAdvance,
    ``Verified.Wasi.Resource.ResourcePrefix.completed,
    ``Verified.Wasi.Resource.ResourcePrefix.advance,
    ``Verified.Wasi.Resource.ResourcePrefix.ofPrefix,
    ``Verified.Wasi.Resource.argumentMoves_slots,
    ``Verified.Wasi.Resource.argumentLive_code,
    ``Verified.Wasi.Resource.argumentKept_code,
    ``Verified.Wasi.Resource.PureContext.argumentCost_compiler,
    ``Verified.Wasi.Resource.loopLive_code,
    ``Verified.Wasi.Resource.loopCaptured_modes,
    ``Verified.Wasi.Resource.loopSlots_modes,
    ``Verified.Wasi.Resource.PureContext.loopCountCost_compiler,
    ``Verified.Wasi.Resource.PureContext.loopInitCost_compiler,
    ``Verified.Wasi.Resource.PureContext.loopTestCost_compiler,
    ``Verified.Wasi.Resource.PureContext.word_ownedCost,
    ``Verified.Wasi.Resource.PureContext.returnWordCost_nil,
    ``Verified.Wasi.Resource.PureContext.readCost_compiler,
    ``Verified.Wasi.Resource.PrefixBound.ret_resources,
    ``Verified.Wasi.Resource.PrefixBound.read_resources,
    ``Verified.Wasi.Resource.PrefixBound.write_resources,
    ``Verified.Wasi.Resource.PrefixBound.exit_resources,
    ``Verified.Wasi.CostCommandResult.erase,
    ``Verified.Wasi.CostFunctionResult.erase,
    ``Verified.Wasi.CostCommandCodeSpec.safety,
    ``Verified.Wasi.cost_command_unit_spec,
    ``Verified.Wasi.cost_command_ret_spec,
    ``Verified.Wasi.cost_command_read_spec,
    ``Verified.Wasi.cost_command_write_spec,
    ``Verified.Wasi.cost_command_exit_spec]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI resource axiom check passed for {theorems.size} theorems"

check_wasi_resource_axioms
