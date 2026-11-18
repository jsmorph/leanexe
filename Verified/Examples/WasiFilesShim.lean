import Verified.Examples.WasiFiles
import Verified.Shim

/-!
The footprint theorem and the descriptor corollary at the specification level for the files
command of `Verified.Examples.WasiFiles`, which writes a file in one bracket of `withOpen` and reads
it back in another, and reads the preopened directory's record and name.  The shim implements
every flat call that the command imports (`calls_supported`).  For every choice of open flags,
layout, launch, and reply sequence, every Talos run of `_start` from the command's initial store,
with no layer events, no exit marker, and no recorded outputs, under the shim's environment with
enough fuel has the footprint of `Footprint` (`linux_footprint`), and the layer events of every
such run name only standard streams and the descriptor numbers that the shim holds open
(`linux_names`).
-/

namespace Verified.Examples.WasiFiles

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- The world at the start of `_start`: no layer events, no exit marker, no recorded outputs, and
no WASI events. -/
def linuxStart : Observed LinuxWorld := ⟨⟨[], none, fun _ => []⟩, []⟩

/-- The command's initial store with the world `linuxStart`. -/
def linuxInitial : Store (Observed LinuxWorld) :=
  compileInitialStoreWith command.sysCalls command.pure.module command.program command.entries
    command.mainEntry command.literalPool linuxStart

theorem calls_supported : ∀ call ∈ command.sysCalls, call ∈ shimCalls := by decide +kernel

theorem linux_footprint (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart true
        (run fuel command.module (Wrappers.effectIndexWith command.sysCalls command.pure.module 1)
          linuxInitial [] (linuxEnv F L I replies command.sysCalls)) := by
  have initialized := command.initial linuxStart
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := true)
    (budget := 0) (linuxEnv_satisfies F L I replies _ calls_supported _
      (by simp [compile_imports_with, ABI.importsWith_length]))
    initialized.1 rfl Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) initialized.2.1 (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

/-- In every run of `linux_footprint`, the layer events name only standard streams and the
descriptor numbers that the shim holds open: each `read` and `write` names descriptor 0, 1, or 2 or
a number of `openNumbers I` after the events before it, and each `openat2` and `close` a number of
`openNumbers I`. -/
theorem linux_names {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {result : Result (Observed LinuxWorld)}
    (footprint : Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart
      true result) :
    ∃ final message, result = .Trap final message ∧ NamesHeld I [] final.host.world.events := by
  cases result with
  | Trap final message => exact ⟨final, message, rfl, footprint_namesHeld footprint rfl⟩
  | _ => exact footprint.elim

end Verified.Examples.WasiFiles

#print axioms Verified.Examples.WasiFiles.linux_footprint
#print axioms Verified.Examples.WasiFiles.linux_names
