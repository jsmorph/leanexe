import Verified.Examples.WasiSys
import Verified.Examples.WasiSysEnviron
import Verified.Shim

/-!
The footprint theorem at the specification level for the commands of increment 2 of the shim: the
flat call example, which calls `args_sizes_get`, `args_get`, `clock_time_get`, and `random_get`,
and the environment example, which calls `environ_sizes_get` and `environ_get`.  The shim
implements every flat call that each command imports (`calls_supported`).  For every open flags,
layout, launch, and reply sequence, every Talos run of `_start` from each command's initial store,
with no layer events, no exit marker, and no recorded outputs, under the shim's environment with
enough fuel has the footprint of `Footprint`: the layer events are images of the run's WASI trace,
which ends at an accepted exit, a rejected exit, a trap of the shim, or a trap of the guest after a
prefix of `main`.
-/

namespace Verified.Examples.WasiSys

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

end Verified.Examples.WasiSys

namespace Verified.Examples.WasiSysEnviron

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- The command's initial store with the world `WasiSys.linuxStart`. -/
def linuxInitial : Store (Observed LinuxWorld) :=
  compileInitialStoreWith command.sysCalls command.pure.module command.program command.entries
    command.mainEntry command.literalPool WasiSys.linuxStart

theorem calls_supported : ∀ call ∈ command.sysCalls, call ∈ shimCalls := by decide +kernel

theorem linux_footprint (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) WasiSys.linuxStart true
        (run fuel command.module (Wrappers.effectIndexWith command.sysCalls command.pure.module 1)
          linuxInitial [] (linuxEnv F L I replies command.sysCalls)) := by
  have initialized := command.initial WasiSys.linuxStart
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := true)
    (budget := 0) (linuxEnv_satisfies F L I replies _ calls_supported _
      (by simp [compile_imports_with, ABI.importsWith_length]))
    initialized.1 rfl Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) initialized.2.1 (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

end Verified.Examples.WasiSysEnviron

#print axioms Verified.Examples.WasiSys.linux_footprint
#print axioms Verified.Examples.WasiSysEnviron.linux_footprint
