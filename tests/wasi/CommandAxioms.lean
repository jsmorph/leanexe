import Verified.Wasi.ReturnCommand
import Verified.Wasi.CommandBind
import Verified.Wasi.CommandValue
import Verified.Wasi.LoopControl

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
    ``Verified.Wasi.wp_loopControl]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Command axiom check passed for {theorems.size} theorems"

check_command_axioms
