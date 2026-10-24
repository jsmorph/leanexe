import Verified.Wasi.ReturnCommand
import Verified.Wasi.CommandBind
import Verified.Wasi.CommandValue
import Verified.Wasi.LoopControl
import Verified.Wasi.LoopSemantics
import Verified.Wasi.CallOwnership
import Verified.Wasi.CallFrame
import Verified.Wasi.CallHelper
import Verified.Wasi.ResultRelease
import Verified.Wasi.CommandLeaves
import Verified.Wasi.CommandCallSpec
import Verified.Wasi.CommandBindSpec
import Verified.Wasi.CommandConditionalSpec
import Verified.Wasi.CommandLoopSpec

open Lean Elab Command in
elab "check_command_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
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
    ``Verified.Wasi.wp_return,
    ``Verified.Wasi.CommandResult.resource_refl,
    ``Verified.Wasi.wp_command_unit,
    ``Verified.Wasi.wp_command_ret,
    ``Verified.Wasi.CommandResult.bind_trap,
    ``Verified.Wasi.CommandResult.bind_after_trap,
    ``Verified.Wasi.CommandResult.bind_unit,
    ``Verified.Wasi.CommandResult.bind_value,
    ``Verified.Wasi.wp_sequence_unit,
    ``Verified.Wasi.After.lower,
    ``Verified.Wasi.ResultTy.fresh_scalar,
    ``Verified.Wasi.After.thenEmpty,
    ``Verified.Wasi.wp_sequence_value,
    ``Verified.Wasi.loop_increment_toNat,
    ``Verified.Wasi.loop_rank_decreases,
    ``Verified.Wasi.wp_loopControl,
    ``Verified.Wasi.loop_residual_done,
    ``Verified.Wasi.loop_remaining_succ,
    ``Verified.Wasi.loop_successor_le,
    ``Verified.Wasi.loop_residual_unfold,
    ``Verified.Wasi.LoopProgress.initial,
    ``Verified.Wasi.LoopProgress.after_return,
    ``Verified.Wasi.LoopProgress.advance,
    ``Verified.Wasi.LoopProgress.resource,
    ``Verified.Wasi.LoopProgress.complete,
    ``Verified.Wasi.LoopProgress.done,
    ``Verified.Wasi.LoopProgress.stopped,
    ``Verified.Wasi.LoopProgress.exited,
    ``Verified.Wasi.LoopProgress.trapped,
    ``Verified.arguments_moved,
    ``Verified.Wasi.EffectSig.callMoves_moved,
    ``Verified.Wasi.relocate_argsCode,
    ``Verified.Wasi.wp_arguments,
    ``Verified.Wasi.EffectSig.placeArgs_facts,
    ``Verified.Wasi.EffectSig.kept_owned,
    ``Verified.Wasi.EffectSig.live_kept,
    ``Verified.Wasi.ArgumentsAfter.ofValues,
    ``Verified.Wasi.ArgumentsAfter.pool_input,
    ``Verified.Wasi.ArgumentsAfter.scratch,
    ``Verified.Wasi.ArgumentsAfter.call,
    ``Verified.Wasi.wp_call_refinement,
    ``Verified.Wasi.wp_effect_helper,
    ``Verified.Wasi.After.release,
    ``Verified.Wasi.command_unit_spec,
    ``Verified.Wasi.command_ret_spec,
    ``Verified.Wasi.command_read_spec,
    ``Verified.Wasi.command_write_spec,
    ``Verified.Wasi.command_exit_spec,
    ``Verified.Wasi.wp_call_after_arguments,
    ``Verified.Wasi.wp_effect_depth,
    ``Verified.Wasi.command_call_spec,
    ``Verified.Wasi.command_bind_unit_spec,
    ``Verified.Wasi.command_ite_spec,
    ``Verified.Wasi.loopCaptured_getD,
    ``Verified.Holds.loopBorrow,
    ``Verified.Holds.Apart.loopBorrow,
    ``Verified.Holds.ApartFrom.loopBorrow,
    ``Verified.Wasi.loopCaptured_safe,
    ``Verified.Wasi.After.reframe,
    ``Verified.Wasi.After.loopAdvance,
    ``Verified.Wasi.After.loopTest,
    ``Verified.Wasi.loop_context_keep,
    ``Verified.Wasi.loop_context_no_dying,
    ``Verified.Wasi.loop_body_step,
    ``Verified.Wasi.CommandResult.loop_body_trap,
    ``Verified.Wasi.wp_loopPrepare,
    ``Verified.Wasi.loopCaptured_cons,
    ``Verified.Wasi.loopCaptured_idempotent,
    ``Verified.Wasi.loop_index_hold,
    ``Verified.Wasi.loop_context_holds,
    ``Verified.Wasi.loop_context_scratch,
    ``Verified.Wasi.loop_context_safe,
    ``Verified.Wasi.loop_test_holds,
    ``Verified.Wasi.loop_test_scratch,
    ``Verified.Wasi.loop_test_safe,
    ``Verified.Wasi.loop_test_step,
    ``Verified.Wasi.wp_loopRelease,
    ``Verified.Wasi.wp_loopTest,
    ``Verified.Wasi.wp_loopBody,
    ``Verified.Wasi.wp_loopFinish,
    ``Verified.Wasi.loop_held_frame,
    ``Verified.Wasi.LoopFrame.retest,
    ``Verified.Wasi.LoopFrame.advance,
    ``Verified.Wasi.wp_loopPrepared,
    ``Verified.Wasi.command_loop_spec]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Command axiom check passed for {theorems.size} theorems"

check_command_axioms
