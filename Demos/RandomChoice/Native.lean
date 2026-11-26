module

public import Demos.RandomChoice.Budget
public import Demos.RandomHistogram.Native

@[expose] public section

/-! The footprint theorems of the unbiased random choice's command at the memory cap of a native
executable.  The shim implements every flat call that the command imports, `args_sizes_get`,
`args_get`, and `random_get` (`calls_supported`).  `nativeStore` holds the module's initial store
with the executable's cap and the world `nativeWorld`, which has no layer events, no exit marker,
and no recorded outputs.  `linux_footprint_native` states that every Talos run of `_start` from that
store under the shim's environment with enough fuel has the footprint of `Footprint`: the layer
events are images of the run's WASI trace, which ends at an accepted exit, a rejected exit, a trap
of the shim, or a trap of the guest after a prefix of `main`.

`linux_footprint_bounded` states the footprint without a guest trap for every N and K, for a launch
whose arguments' strings, each with its zero byte, and eight-byte pointers take at most the random
histogram's `argsLimit`, 6 MiB, at a cap whose pages hold `budget` above the heap's start.  The
shim answers `args_sizes_get` with the count and size of the launch's arguments
(`linux_sizes`), so the block that the reply asks for fits `argsLimit` (`reportedSize_le`), and
`call_prefix_bound` gives the budget premise.
`budget_fits` states that `budget` fits the 4,096 pages of the native executable above the heap's
start at byte 4,096. -/

namespace Demos.RandomChoice

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim Verified.ShimA64

theorem calls_supported : ∀ call ∈ command.sysCalls, call ∈ shimCalls := by decide +kernel

theorem linux_footprint_native (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (replies : Linux.Replies) {cap : Nat} (hcap : cap ≤ 65535) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) nativeWorld true
        (run fuel command.module startIndex (nativeStore command.module cap nativeWorld) []
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

theorem budget_fits : 4096 + budget ≤ 65536 * 4096 := by
  rw [budget_value]
  decide

/-- The footprint of `linux_footprint_native` without a guest trap, for every N and K, at a cap
whose pages hold the budget above the heap's start at byte 4,096, for a launch whose arguments'
strings and eight-byte pointers take at most `argsLimit` bytes. -/
theorem linux_footprint_bounded (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (R : Linux.Replies)
    (small : stringsSize I.args + 8 * I.args.length ≤ RandomHistogram.argsLimit) {cap : Nat}
    (hcap : cap ≤ 65535) (room : 4096 + budget ≤ 65536 * cap) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I R (main.bind fun status => Action.exit status) nativeWorld false
        (run fuel command.module startIndex (nativeStore command.module cap nativeWorld) []
          (linuxEnv F L I R command.sysCalls)) := by
  have initialized := command.initial nativeWorld
  have hat := initialized.1
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I R) (aborts := false)
    (initial := nativeStore command.module cap nativeWorld) (budget := budget)
    (linuxEnv_satisfies F L I R _ calls_supported _
      (by simp [compile_imports_with, ABI.importsWith_length]))
    ⟨hat.globals, hat.freeList, hat.base, hat.top, hat.pages, hat.above, hat.below⟩ rfl
    Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) hcap
    (fun _ => ⟨by change 4096 + budget ≤ 65536 * cap; exact room,
      call_prefix_bound (fun _ _ _ step => by
        rw [linux_sizes step]
        exact reportedSize_le (by decide) (by decide) small) _⟩)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I R (results fuel enough)⟩

#print axioms calls_supported
#print axioms linux_footprint_native
#print axioms linux_footprint_bounded

end Demos.RandomChoice
