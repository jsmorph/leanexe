import Verified.Examples.WasiFiles
import Verified.Shim

/-!
The footprint theorem at the specification level for the command of increment 3 of the shim,
which writes a file in one bracket of `withOpen` and reads it back in another, and reads the
preopened directory's record and name.  The shim implements every flat call that the command
imports (`calls_supported`).  For every open flags, layout, launch, and reply sequence, every
Talos run of `_start` from the command's initial store, with no layer events, no exit marker, and
no recorded outputs, under the shim's environment with enough fuel has the footprint of
`Footprint` (`linux_footprint`).  The command passes the handle check, so its runs keep the
discipline of `withOpen` (`bracketed`), and when the kernel's `openat2` returns only descriptors
that are not open, the layer events of every such run name only open descriptors
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

/-- The runs of `main` and its exit keep the discipline of `withOpen`. -/
theorem bracketed : (main.bind fun status => Action.exit (α := Unit) status).BracketRuns :=
  bracketRuns_command command.pure.funs command.program command.handleMarks command.handlesChecked
    { name := "main", callee := id Verified.Wasi.EffectVar.here } Verified.Env.nil rfl main
    command.main.related

/-- In every run of `linux_footprint`, when the kernel's `openat2` returns only descriptors that
are not open, the layer events name only open descriptors: each `read`, `write`, `openat2`, and
`close` names descriptor 0, 1, 2, or 3 or one that an earlier `openat2` returned and no `close` has
released, and no `close` closes 0 to 3. -/
theorem linux_names {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}
    {result : Result (Observed LinuxWorld)}
    (footprint : Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart
      true result) :
    ∃ final message, result = .Trap final message ∧
      (Linux.FreshOpens [0, 1, 2, 3] final.host.world.events →
        NamesOpen final.host.world.events) := by
  cases result with
  | Trap final message =>
    exact ⟨final, message, rfl, fun fresh => footprint_namesOpen bracketed footprint rfl fresh⟩
  | _ => exact footprint.elim

end Verified.Examples.WasiFiles

#print axioms Verified.Examples.WasiFiles.linux_footprint
#print axioms Verified.Examples.WasiFiles.linux_names
