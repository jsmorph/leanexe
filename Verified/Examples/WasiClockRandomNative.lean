module

public import Verified.Examples.WasiClockRandom
public import Verified.ShimA64.Elf

@[expose] public section

/-!
The footprint theorem for the clock and random example at the memory cap of a native executable.
The shim implements both flat calls that the command imports (`calls_supported`).  For every open
flags, layout, launch, and reply sequence, every Talos run of `_start` from the module's initial
store with the cap `cap` and the world `nativeWorld`, under the shim's environment with enough
fuel, has the footprint of `Footprint`: the layer events are images of the run's WASI trace, which
ends at an accepted exit, a rejected exit, a trap of the shim, or a trap of the guest after a
prefix of `main`.
-/

namespace Verified.Examples.WasiClockRandom

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim Verified.ShimA64

theorem calls_supported : ∀ call ∈ command.sysCalls, call ∈ shimCalls := by decide +kernel

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

end Verified.Examples.WasiClockRandom

#print axioms Verified.Examples.WasiClockRandom.linux_footprint_native
