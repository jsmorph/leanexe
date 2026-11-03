import Library.Sorting.Shellsort.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of Shellsort.  By the compiler's rules, which the verified
compiler's manual states, the compiler translates the tail recursions of `shift`, `insertBy`,
`passes`, and `firstIncrement`, and the loops of `pass` and `straightInsertion`, into loops, so no
theorem of the module has a call-depth premise.  `shellsort` consumes its array, which the caller
hands over as `Moved (Array UInt64)`, and the generated bound is 0.  `shellsort_implements`
composes the generated `compiled.shellsort.trapFree` with `shellsort_eq`. -/

namespace Library.Sorting.Shellsort

open Wasm LeanExe.Pipeline
open Library.Sorting.StraightInsertion (shift straightInsertion)

verified_compile compiled := [shift, straightInsertion, insertBy, pass, passes, firstIncrement,
  shellsort]

theorem shellsort_export :
    ({ name := "shellsort", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 8, the export `shellsort`, called with an array that the caller hands over, from a heap
with the allocator invariant, a memory cap of at most 65,535 pages, and room for
`compiled.shellsort.bound`, returns without a trap the owned array `expected xs`, the elements in
nondecreasing order, and raises `top` by at most the bound. -/
theorem shellsort_implements :
    ImplementsA false compiled.module 8 (fun x : Moved (Array UInt64) => expected x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.shellsort.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.shellsort.bound x) :=
  Verified.implementsA_congr compiled.shellsort.trapFree fun _ _ _ x ⟨_, _, hxs⟩ =>
    shellsort_eq x.val (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The generated bound is 0, so a call does not raise `top`. -/
theorem shellsort_bound (xs : Array UInt64) : compiled.shellsort.bound { val := xs } = 0 :=
  compiled.shellsort.bound_eq xs

#print axioms shellsort_implements

end Library.Sorting.Shellsort
