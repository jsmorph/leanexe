import Verified.Examples.WasiReadAllShim
import Verified.ShimA64.Elf

/-!
The footprint theorem for the readAll command at the memory cap of a native executable.  The
compiled module declares a cap of 65,535 pages, and a native executable reserves a smaller linear
memory, whose page count becomes the store's cap: `nativeStore` holds the module's initial store
with the cap `cap` and the world `nativeWorld`.  The command's facts about its initial store, the
allocator's heap, the literal pool, and the cap, read only the store's globals and memory and the
cap, so they hold at every cap up to 65,535, and `linux_footprint_native` states the footprint of
`linux_footprint` for runs from that store.
-/

namespace Verified.Examples.WasiReadAll

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim Verified.ShimA64

theorem linux_footprint_native (L : ShimLayout) (replies : Linux.Replies) {cap : Nat}
    (hcap : cap ≤ 65535) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint L replies (main.bind fun status => Action.exit status) nativeWorld true
        (run fuel command.module (Wrappers.effectIndex command.pure.module 2)
          (nativeStore command.module cap nativeWorld) [] (linuxEnv L replies)) := by
  have initialized := command.initial nativeWorld
  have hat := initialized.1
  obtain ⟨bound, results⟩ := command.start (host := linuxHost L replies) (aborts := true)
    (initial := nativeStore command.module cap nativeWorld) (budget := 0)
    (linuxEnv_satisfies L replies _ (by rw [compile_imports, ABI.imports_length]))
    ⟨hat.globals, hat.freeList, hat.base, hat.top, hat.pages, hat.above, hat.below⟩ rfl
    Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) hcap (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result L replies (results fuel enough)⟩

end Verified.Examples.WasiReadAll

#print axioms Verified.Examples.WasiReadAll.linux_footprint_native
