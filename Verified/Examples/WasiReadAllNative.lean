import Verified.Examples.WasiReadAllShim
import Verified.ShimA64.Elf

/-!
The footprint theorem for the readAll command at the memory cap of a native executable.  The
compiled module declares a cap of 65,535 pages, and a native executable reserves a smaller linear
memory, whose page count becomes the store's cap: `nativeStore` holds the module's initial store
with the cap `cap` and the world `nativeWorld`.  The command's facts about its initial store, the
allocator's heap, the literal pool, and the cap, read only the store's globals and memory and the
cap, so they hold at every cap up to 65,535, and `linux_footprint_native` states the footprint of
`linux_footprint` for runs from that store.  `main_streams` states that the command's action makes
no flat call, so the trace of no run of it holds one.
-/

namespace Verified.Examples.WasiReadAll

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim Verified.ShimA64

theorem linux_footprint_native (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (replies : Linux.Replies) {cap : Nat} (hcap : cap ≤ 65535) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) nativeWorld true
        (run fuel command.module (Wrappers.effectIndex command.pure.module 2)
          (nativeStore command.module cap nativeWorld) [] (linuxEnv F L I replies [])) := by
  have initialized := command.initial nativeWorld
  have hat := initialized.1
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := true)
    (initial := nativeStore command.module cap nativeWorld) (budget := 0)
    (linuxEnv_satisfies F L I replies [] (fun _ member => nomatch member) _
      (by simp [compile_imports, ABI.imports_length]))
    ⟨hat.globals, hat.freeList, hat.base, hat.top, hat.pages, hat.above, hat.below⟩ rfl
    Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) hcap (fun impossible => nomatch impossible)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

/-- The command's action reads, writes, and exits, and makes no flat call. -/
theorem main_streams : StreamAction (main.bind fun status => Action.exit (α := Unit) status) := by
  refine StreamAction.bind _ ?_ fun _ => trivial
  unfold main
  refine StreamAction.bind _ ?_ fun input => ?_
  · unfold readAll
    split
    · exact ⟨fun _ _ => StreamAction.bind _ (fun _ => trivial) fun _ => trivial, fun _ => trivial⟩
    · trivial
  · split
    · trivial
    · refine StreamAction.bind _ ?_ fun _ => ?_
      · exact ⟨fun _ _ => StreamAction.bind _ (fun _ => trivial) fun _ => by split <;> trivial,
          fun _ => trivial⟩
      · split <;> trivial

end Verified.Examples.WasiReadAll

#print axioms Verified.Examples.WasiReadAll.linux_footprint_native
#print axioms Verified.Examples.WasiReadAll.main_streams
