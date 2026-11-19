import Demos.RandomHistogram.Budget
import Verified.Shim
import Verified.Shim.Args
import Verified.ShimA64.Elf

/-! The footprint theorem of the random-residue histogram's command at the memory cap of a native
executable.  The shim implements every flat call that the command imports, `args_sizes_get`,
`args_get`, and `random_get` (`calls_supported`).  A native executable reserves a smaller linear
memory than the module's declared cap of 65,535 pages, and `nativeStore` holds the module's
initial store with the executable's cap `cap` and the world `nativeWorld`, which has no layer
events, no exit marker, and no recorded outputs.  The command's facts about its initial store read
only the store's globals and memory and the cap, so they hold at every cap up to 65,535, and
`linux_footprint_native` states that every Talos run of `_start` from that store under the
shim's environment with enough fuel has the footprint of `Footprint`: the layer events are images
of the run's WASI trace, which ends at an accepted exit, a rejected exit, a trap of the shim, or a
trap of the guest after a prefix of `main`.

`linux_footprint_bounded` states the footprint without a guest trap for a launch whose arguments'
strings, each with its zero byte, and eight-byte pointers take at most `argsLimit` bytes, for every
N, at a cap whose pages hold `budget` above the heap's start.  The shim answers `args_sizes_get`
with the count and size of the launch's arguments (`linux_sizes` of `Verified/Shim/Args.lean`),
so the block that the reply asks for fits `argsLimit` (`reportedSize_le`), and
`call_prefix_bound` gives the budget premise from `body_bounded`. -/

namespace Demos.RandomHistogram

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

/-- The budget of `main` holds under the shim's host for a launch whose strings and eight-byte
pointers of its arguments take at most `argsLimit` bytes. -/
theorem call_prefix_bound (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies)
    (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (world : Observed LinuxWorld) :
    Resource.CallPrefixBound (observedHost (linuxHost F L I R))
      (.ofProg command.pure.program command.pure.funs) command.program .here 0 .nil world
      budget := by
  have bound : ∀ world outputs after, (linuxHost F L I R).sys world Call.argsGet.reporterCall []
      (.returned 0 outputs) after → Resource.reportedSize outputs ≤ argsLimit := fun _ _ _ step => by
    rw [linux_sizes step]
    exact reportedSize_le (by decide) (by decide) small
  intro trace residual final spent fits progress
  exact Resource.call_prefix_rule budget progress rfl ((body_bounded bound).2 world)

/-- The footprint of `linux_footprint_native` without a guest trap, at a cap whose pages hold the
budget above the heap's start at byte 4,096, for a launch whose arguments meet the premises of
`call_prefix_bound`. -/
theorem linux_footprint_bounded (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (R : Linux.Replies) (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit) {cap : Nat}
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
      call_prefix_bound F L I R small _⟩)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I R (results fuel enough)⟩

#print axioms calls_supported
#print axioms linux_footprint_native
#print axioms call_prefix_bound
#print axioms linux_footprint_bounded

end Demos.RandomHistogram
