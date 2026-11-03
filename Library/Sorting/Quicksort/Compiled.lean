import Library.Sorting.Quicksort.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of quicksort.  The compiler translates the tail recursions of
`scanUp`, `scanDown`, `part`, and `stages`, and the loop of straight insertion, into loops, so the
call stack does not grow.  `quicksort` consumes its array, which the caller moves as
`Moved (Array UInt64)`, and allocates the stack of 64 entries.  `quicksort_implements` composes
the generated `compiled.quicksort.trapFree` with `quicksort_eq`. -/

namespace Library.Sorting.Quicksort

open Wasm LeanExe.Pipeline
open Library.Sorting.Heapsort (swap)
open Library.Sorting.StraightInsertion (shift straightInsertion)

set_option maxHeartbeats 1000000 in
verified_compile compiled := [swap, shift, straightInsertion, scanUp, scanDown, part, stages,
  quicksort]

theorem quicksort_export :
    ({ name := "quicksort", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 9, the export `quicksort`, called with an array that the caller moves, from a heap
with the allocator invariant, a memory cap of at most 65,535 pages, and room for
`compiled.quicksort.bound`, returns without a trap the owned array `expected xs`, the elements in
nondecreasing order, and raises `top` by at most the bound. -/
theorem quicksort_implements :
    ImplementsA false compiled.module 9 (fun x : Moved (Array UInt64) => expected x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.quicksort.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.quicksort.bound x) :=
  Verified.implementsA_congr compiled.quicksort.trapFree fun _ _ _ x ⟨_, _, hxs⟩ =>
    quicksort_eq x.val (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The module's storage beyond the array is one block of 128 words, the stack of 64 entries. -/
theorem quicksort_bound (xs : Array UInt64) :
    compiled.quicksort.bound { val := xs } = Verified.blockCost 128 :=
  compiled.quicksort.bound_eq xs

#print axioms quicksort_implements

end Library.Sorting.Quicksort
