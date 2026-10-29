import Verified.AlignedRelease
import LeanExe.Pipeline.AlignedAlloc

/-!
The second stage's interfaces, proved for the runtime's functions.  `Runtime.allocAligned`
discharges `AllocAligned` from `alloc_spec_runsA`, with the abort flag set, since the statement
covers the runs that trap when memory cannot grow.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The runtime's `alloc` makes only aligned 64-bit accesses from an aligned heap. -/
theorem Runtime.allocAligned {m : Module} (hm : Runtime m) : AllocAligned m := by
  intro env heap store bytes vs hAt hAligned hBytes hCap
  exact ((alloc_spec_runsA true hm.memory32 hm.imports hm.alloc env heap store bytes hAt hAligned
    hBytes hCap nofun).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.alloc)
    rfl vs).2

end Verified
