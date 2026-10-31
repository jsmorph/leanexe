import Library.Sorting.Heapsort.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of heapsort.  The compiler translates the tail recursion of
`siftDown` into a loop, and `heapsort` consumes its array, which the caller hands over as
`Moved (Array UInt64)`: every update is the array's last use, so the module sorts the array in its
own block.  `heapsort_implements` composes the generated `compiled.heapsort.trapFree` with
`heapsort_eq`. -/

namespace Library.Sorting.Heapsort

open Wasm LeanExe.Pipeline

verified_compile compiled := [swap, siftDown, heapify, heapsort]

theorem heapsort_export :
    ({ name := "heapsort", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `heapsort`, called with an array that the caller hands over, from a heap
with room for `compiled.heapsort.bound`, returns without a trap the owned array `expected xs`, the
elements in nondecreasing order, and raises `top` by at most the bound. -/
theorem heapsort_implements :
    ImplementsA false compiled.module 5 (fun x : Moved (Array UInt64) => expected x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.heapsort.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.heapsort.bound x) :=
  Verified.implementsA_congr compiled.heapsort.trapFree fun _ _ _ x ⟨_, _, hxs⟩ =>
    heapsort_eq x.val (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The module allocates nothing: it sorts the array in its own block. -/
theorem heapsort_bound (xs : Array UInt64) : compiled.heapsort.bound { val := xs } = 0 :=
  compiled.heapsort.bound_eq xs

#print axioms heapsort_implements

end Library.Sorting.Heapsort
