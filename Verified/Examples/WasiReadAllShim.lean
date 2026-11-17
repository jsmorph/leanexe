import Verified.Examples.WasiReadAll
import Verified.Shim

/-!
The footprint theorem at the specification level for the readAll command.  For every open flags,
layout, launch, and reply sequence, every Talos run of `_start` from the command's initial store,
with no layer events, no exit marker, and no recorded outputs, under the shim's environment with
enough fuel has the footprint of `Footprint`: the run ends at an accepted exit, a rejected exit, a
trap of the shim, or a trap of the guest after a prefix of `main`, and the layer events are images
of its WASI trace.  The reads of descriptor 0 and the writes of descriptor 1 in those events moved
the bytes that the trace's `fd_read` and `fd_write` events committed.
-/

namespace Verified.Examples.WasiReadAll

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- The world at the start of `_start`: no layer events, no exit marker, no recorded outputs, and
no WASI events. -/
def linuxStart : Observed LinuxWorld := ⟨⟨[], none, fun _ => []⟩, []⟩

/-- The command's initial store with the world `linuxStart`. -/
def linuxInitial : Store (Observed LinuxWorld) :=
  compileInitialStore command.pure.module command.program command.entries command.mainEntry
    command.literalPool linuxStart

theorem linux_footprint (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart true
        (run fuel command.module (Wrappers.effectIndex command.pure.module 2) linuxInitial []
          (linuxEnv F L I replies [])) := by
  have initialized := command.initial linuxStart
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := true)
    (budget := 0) (linuxEnv_satisfies F L I replies [] (fun _ member => nomatch member) _
      (by simp [compile_imports, ABI.imports_length]))
    initialized.1 rfl Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) initialized.2.1 (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

/-- In every run of `linux_footprint`, the layer's reads of descriptor 0 returned the bytes that
the trace's `fd_read` events committed, and its writes of descriptor 1 took the bytes that the
trace's `fd_write` events to standard output committed. -/
theorem linux_bytes {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {result : Result (Observed LinuxWorld)}
    (footprint : Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart
      true result) :
    ∃ final message trace, result = .Trap final message ∧
      Linux.readData 0 final.host.world.events = committedReads 0 trace ∧
      Linux.writeData 1 final.host.world.events = committedWrites 1 trace ∧
      final.host.events = trace := by
  cases result with
  | Trap final message =>
    obtain ⟨trace, ls, grown, images, _, _, events, _⟩ := footprint
    refine ⟨final, message, trace, rfl, ?_, ?_, ?_⟩
    · rw [grown]
      exact images.readData 0
    · rw [grown]
      exact images.writeData 1
    · exact events
  | _ => exact footprint.elim

end Verified.Examples.WasiReadAll

#print axioms Verified.Shim.shim_footprint
#print axioms Verified.Examples.WasiReadAll.linux_footprint
#print axioms Verified.Examples.WasiReadAll.linux_bytes
