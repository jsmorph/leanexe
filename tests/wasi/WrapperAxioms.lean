import Verified.Wasi.ReadFrame
import Verified.Wasi.Write
import Verified.Wasi.ReadCall
import Verified.Wasi.Runtime
import Verified.Wasi.RuntimeFrame
import Verified.Wasi.ReadFunction
import Verified.Wasi.Exit

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
    ``Verified.Wasi.wp_exit,
    ``LeanExe.Wasi.Exec.exited_marker]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Wrapper axiom check passed for {theorems.size} theorems"

check_wrapper_axioms
