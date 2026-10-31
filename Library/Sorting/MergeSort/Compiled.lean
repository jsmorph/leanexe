import Library.Sorting.MergeSort.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of merge sort.  The compiler translates the tail recursions of
`merge`, `pass`, and `sortLoop` into loops.  `mergeSort` consumes its array, which the caller hands
over as `Moved (Array UInt64)`, and each pass writes into a new array of the same length and
releases the old one.  `mergeSort_implements` composes the generated
`compiled.mergeSort.trapFree` with `mergeSort_eq`. -/

namespace Library.Sorting.MergeSort

open Wasm LeanExe.Pipeline

verified_compile compiled := [runEnd, merge, pass, sortLoop, mergeSort]

theorem mergeSort_export :
    ({ name := "mergeSort", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 6, the export `mergeSort`, called with an array that the caller hands over, from a
heap with room for `compiled.mergeSort.bound`, returns without a trap the owned array
`expected xs`, the elements in nondecreasing order, and raises `top` by at most the bound. -/
theorem mergeSort_implements :
    ImplementsA false compiled.module 6 (fun x : Moved (Array UInt64) => expected x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.mergeSort.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.mergeSort.bound x) :=
  Verified.implementsA_congr compiled.mergeSort.trapFree fun _ _ _ x ⟨_, _, hxs⟩ =>
    mergeSort_eq x.val (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The room a call needs: the bound of the passes, each of which charges the block of the new
array of `n` words. -/
theorem mergeSort_bound (xs : Array UInt64) :
    compiled.mergeSort.bound { val := xs } =
      compiled.sortLoop.bound (1, xs.size.toUInt64, { val := xs }) :=
  compiled.mergeSort.bound_eq xs

#print axioms mergeSort_implements

end Library.Sorting.MergeSort
