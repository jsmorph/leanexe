import Verified.Wasi.ReadFrame
import Verified.Wasi.Write
import Verified.Wasi.ReadCall
import Verified.Wasi.Runtime
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
    ``Verified.Wasi.wp_exit]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"Wrapper axiom check passed for {theorems.size} theorems"

check_wrapper_axioms
