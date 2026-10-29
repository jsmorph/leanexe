import Verified.AlignedRelease
import LeanExe.Pipeline.AlignedAlloc
import LeanExe.ProofKit.AlignedReleaseTree

/-!
The second stage's interfaces, proved for the runtime's functions.  `Runtime.allocAligned`
discharges `AllocAligned` from `alloc_spec_runsA`, with the abort flag set, since the statement
covers the runs that trap when memory cannot grow.  `Runtime.releaseAligned` discharges the three
fields of `ReleaseAligned` from `release_null_runA`, `release_leaf_runA` with
`Heap.Aligned.release`, and `release_tree_run_topA`, each extended to the caller's further
arguments by `RunsA.append_args`.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The runtime's `alloc` makes only aligned 64-bit accesses from an aligned heap. -/
theorem Runtime.allocAligned {m : Module} (hm : Runtime m) : AllocAligned m := by
  intro env heap store bytes vs hAt hAligned hBytes hCap
  exact ((alloc_spec_runsA true hm.memory32 hm.imports hm.alloc env heap store bytes hAt hAligned
    hBytes hCap nofun).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.alloc)
    rfl vs).2

/-- The runtime's `release` makes only aligned 64-bit accesses from an aligned heap and objects
whose blocks start and end at multiples of 8, and the heap after it is aligned. -/
theorem Runtime.releaseAligned {m : Module} (hm : Runtime m) : ReleaseAligned m where
  null env store vs :=
    ((release_null_runA hm.imports hm.release env store).append_args (by simp [hm.imports])
      (by simpa [hm.imports] using hm.release) rfl vs).2
  leaf env heap store ptr vs hAt hAligned hObject hMagic hCount hMask hPtrAl hCapAl :=
    ⟨((release_leaf_runA hm.imports hm.release env heap store ptr hAt hObject hMagic hCount hMask
      hAligned hPtrAl).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release)
      rfl vs).2, hAligned.release hPtrAl hCapAl⟩
  tree env heap store p n vs hAt hAligned hOwned hDisjoint hBlocksAl :=
    ((release_tree_run_topA hm.imports hm.release env heap store p n hAt hOwned hDisjoint hAligned
      hBlocksAl).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release) rfl
      vs).mono fun _ _ ⟨_, hOut, rfl, hPost⟩ => ⟨by simpa using hOut, hPost⟩

end Verified
