import Verified.Examples.WasiSysShim
import Verified.ShimA64.Elf

/-!
The footprint theorem for the flat call example at the memory cap of a native executable.  A
native executable reserves a smaller linear memory than the module's declared cap of 65,535 pages,
and `nativeStore` holds the module's initial store with the executable's cap `cap` and the world
`nativeWorld`.  The command's facts about its initial store read only the store's globals and
memory and the cap, so they hold at every cap up to 65,535, and `linux_footprint_native` states
the footprint of `linux_footprint` for runs from that store under the shim's environment with the
command's flat calls, `args_sizes_get`, `args_get`, `clock_time_get`, and `random_get`.
-/

namespace Verified.Examples.WasiSys

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

end Verified.Examples.WasiSys

#print axioms Verified.Examples.WasiSys.linux_footprint_native
