module

public import Verified.Examples.WasiFilesShim
public import Verified.ShimA64.Elf

@[expose] public section

/-!
The footprint theorem for the files command at the memory cap of a native executable.  The
compiled module declares a cap of 65,535 pages, and a native executable reserves a smaller linear
memory, whose page count becomes the store's cap: `nativeStore` holds the module's initial store
with the cap `cap` and the world `nativeWorld`.  The shim implements every flat call that the
command imports (`calls_supported`), and `linux_footprint_native` states the footprint of
`Footprint` for every run of `_start` from that store under the shim's environment with enough
fuel, for every open flags, layout, launch, and reply sequence.  The layer events of every such
run name only standard streams and the descriptor numbers that the shim holds open
(`linux_names_native`).
-/

namespace Verified.Examples.WasiFiles

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim Verified.ShimA64

theorem linux_footprint_native (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (replies : Linux.Replies) {cap : Nat} (hcap : cap ≤ 65535) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) nativeWorld true
        (run fuel command.module (Wrappers.effectIndexWith command.sysCalls command.pure.module 1)
          (nativeStore command.module cap nativeWorld) []
          (linuxEnv F L I replies command.sysCalls)) := by
  have initialized := command.initial nativeWorld
  have hat := initialized.1
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := true)
    (initial := nativeStore command.module cap nativeWorld) (budget := 0)
    (linuxEnv_satisfies F L I replies _ calls_supported _
      (by simp [compile_imports_with, ABI.importsWith_length]))
    ⟨hat.globals, hat.freeList, hat.base, hat.top, hat.pages, hat.above, hat.below⟩ rfl
    Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) hcap (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

/-- In every run of `linux_footprint_native`, the layer events name only standard streams and the
descriptor numbers that the shim holds open. -/
theorem linux_names_native {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {result : Result (Observed LinuxWorld)}
    (footprint : Footprint F L I replies (main.bind fun status => Action.exit status) nativeWorld
      true result) :
    ∃ final message, result = .Trap final message ∧ NamesHeld I [] final.host.world.events := by
  cases result with
  | Trap final message => exact ⟨final, message, rfl, footprint_namesHeld footprint rfl⟩
  | _ => exact footprint.elim

end Verified.Examples.WasiFiles

#print axioms Verified.Examples.WasiFiles.linux_footprint_native
#print axioms Verified.Examples.WasiFiles.linux_names_native
