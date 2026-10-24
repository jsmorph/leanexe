import Verified.Wasi.ReadFrame
import Verified.Wasi.Write
import Verified.Wasi.ReadCall
import Verified.Wasi.Runtime
import Verified.Wasi.RuntimeFrame
import Verified.Wasi.ReadFunction
import Verified.Wasi.CallWrappers
import Verified.Wasi.WriteHelper
import Verified.Wasi.ScratchContext
import Verified.Wasi.AfterScratch
import Verified.Wasi.ReadCommand
import Verified.Wasi.WriteCommand
import Verified.Wasi.Exit
import Verified.Wasi.ExitCommand
import Verified.Wasi.OwnedScratch
import Verified.Wasi.FunctionEntry
import Verified.Wasi.FunctionRun
import Verified.Wasi.CommandIte
import Verified.Wasi.CommandConditional
import Verified.Wasi.FunctionEntryBudget
import Verified.Wasi.FunctionRunBudget
import Verified.Wasi.CommandResultStore
import Verified.Wasi.CostConditionalSpec
import Verified.Wasi.FunctionDispatcher
import Verified.Wasi.CostFunctionLift

open Lean Elab Command in
elab "check_wrapper_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``Verified.Wasi.GuestFrame.weaken,
    ``Verified.Wasi.GuestFrame.heap,
    ``Verified.Wasi.GuestFrame.step,
    ``Verified.Wasi.GuestFrame.trans,
    ``Verified.Wasi.GuestFrame.scratchHeap,
    ``Verified.Wasi.GuestFrame.scratchStep,
    ``Verified.Wasi.GuestFrame.scratchRep,
    ``Verified.Wasi.GuestFrame.readStep,
    ``Verified.Wasi.allocated_afterRead,
    ``Verified.Wasi.wp_write,
    ``Verified.Wasi.wp_read_call,
    ``Verified.Wasi.alloc_runs,
    ``Verified.Wasi.release_runs,
    ``Verified.Wasi.wp_alloc,
    ``Verified.Wasi.wp_release,
    ``Verified.Wasi.wp_call_runs_frame,
    ``Verified.Wasi.wp_alloc_frame,
    ``Verified.Wasi.read_payload_region,
    ``Verified.Wasi.read_capacity,
    ``Verified.Wasi.read_empty_at,
    ``Verified.Wasi.read_buffer,
    ``Verified.Wasi.wp_discard_read,
    ``Verified.Wasi.read_allocation_buffer,
    ``Verified.Wasi.wp_read_allocate,
    ``Verified.Wasi.wp_read_overflow,
    ``Verified.Wasi.read_fresh_step,
    ``Verified.Wasi.read_discard_step,
    ``Verified.Wasi.read_discard_top,
    ``Verified.Wasi.ReadReady.frame_step,
    ``Verified.Wasi.ReadReady.reply_rep,
    ``Verified.Wasi.wp_read_result,
    ``Verified.Wasi.wp_read_invoke,
    ``Verified.Wasi.readCost_positive,
    ``Verified.Wasi.read_room_of_budget,
    ``Verified.Wasi.readCode_parts,
    ``Verified.Wasi.wp_read_return,
    ``Verified.Wasi.wp_read,
    ``Verified.Wasi.readFunction_run,
    ``Verified.Wasi.readFunction_run_with_budget,
    ``Verified.Wasi.wp_call_returned_at,
    ``Verified.Wasi.wp_call_trapped_at,
    ``Verified.Wasi.wp_read_helper,
    ``Verified.Wasi.wp_read_helper_with_budget,
    ``Verified.Wasi.writeFunction_run,
    ``Verified.Wasi.write_buffer_abi,
    ``Verified.Wasi.wp_write_helper,
    ``Verified.Wasi.wp_write_helper_at,
    ``Verified.Holds.ApartFrom.agree,
    ``Verified.Holds.ApartFrom.transfer,
    ``Verified.Holds.ApartFrom.push,
    ``Verified.Holds.ApartFrom.pop,
    ``Verified.Holds.KeepDying.transfer_kept,
    ``Verified.Holds.step_scratch,
    ``Verified.Holds.step_scratch_dying,
    ``Verified.Wasi.GuestFrame.scratchHolds,
    ``Verified.Wasi.bytes_scratch,
    ``Verified.Wasi.After.values,
    ``Verified.Wasi.After.ofValues,
    ``Verified.Wasi.After.scratch,
    ``Verified.Wasi.After.keepDying,
    ``Verified.Wasi.After.pool_safe,
    ``Verified.Wasi.After.thenUnit,
    ``Verified.Wasi.After.thenWord,
    ``Verified.Wasi.After.bind_value,
    ``Verified.Wasi.read_result_rep,
    ``Verified.Wasi.read_result_regions,
    ``Verified.Wasi.read_after,
    ``Verified.Wasi.wp_read_command_call,
    ``Verified.Wasi.wp_command_read,
    ``Verified.Wasi.wp_command_read_budget,
    ``Verified.Wasi.write_after,
    ``Verified.Wasi.wp_write_command_call,
    ``Verified.Wasi.wp_release_context,
    ``Verified.Wasi.write_after_release,
    ``Verified.Wasi.wp_command_write,
    ``Verified.Wasi.block_scratch,
    ``Verified.Wasi.node_blocks_scratch,
    ``Verified.Wasi.slots_blocks_scratch,
    ``Verified.Wasi.owned_scratch,
    ``Verified.Wasi.ResultTy.Rep.scratch,
    ``Verified.Wasi.wp_exit,
    ``Verified.Wasi.wp_command_exit,
    ``Verified.Wasi.exec_pure_shape,
    ``Verified.Wasi.params_holds,
    ``Verified.Wasi.params_scratch,
    ``Verified.Wasi.params_get,
    ``Verified.Wasi.copied_params_hold,
    ``Verified.Wasi.wp_guard_entry,
    ``Verified.Wasi.wp_function_parameters,
    ``Verified.Wasi.wp_parameter_cleanup,
    ``Verified.Wasi.wp_function_entry,
    ``Verified.Wasi.ResultTy.Rep.length,
    ``Verified.Wasi.ResultTy.types_length,
    ``Verified.Wasi.keep_params,
    ``Verified.Wasi.function_after_step,
    ``Verified.Wasi.function_result_after,
    ``Verified.Wasi.function_post_body,
    ``Verified.Wasi.function_body_wp,
    ``Verified.Wasi.effectFunction_run,
    ``Verified.Wasi.ResultTy.Rep.typed,
    ``Verified.Wasi.wp_ite_bool,
    ``Verified.Wasi.wp_store_command_result,
    ``Verified.Wasi.wp_ite_branch,
    ``Verified.Wasi.wp_command_ite,
    ``Verified.Wasi.wp_parameter_cleanup_framed,
    ``Verified.Wasi.wp_function_entry_framed,
    ``Verified.Wasi.function_body_wp_with_aborts,
    ``Verified.Wasi.wp_store_owned_result,
    ``Verified.Wasi.Resource.PureContext.returnBoolCost_nil,
    ``Verified.Wasi.Resource.ResourceExec.ite_selected,
    ``Verified.Wasi.Resource.PrefixBound.ite_selected,
    ``Verified.Wasi.Resource.PrefixBound.ite_resources,
    ``Verified.Wasi.cost_command_ite_spec,
    ``Verified.Wasi.effectFunction_run_post,
    ``Verified.Wasi.CostFunctionResult.there,
    ``Verified.Wasi.CostEffectSpec.there,
    ``LeanExe.Wasi.Exec.exited_marker]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Wrapper axiom check passed for {theorems.size} theorems"

check_wrapper_axioms
