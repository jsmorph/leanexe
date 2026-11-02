import Library.Sorting.Find.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of selection.  The compiler translates the tail recursions of
`scanUp`, `scanDown`, `part`, and `find` into loops, so the call stack does not grow.  `select`
consumes its array, which the caller hands over as `Moved (Array UInt64)`, and the module allocates
nothing.  `select_implements` composes the generated `compiled.select.trapFree` with `select_eq`. -/

namespace Library.Sorting.Find

open Wasm LeanExe.Pipeline
open Library.Sorting.Heapsort (swap)
open Library.Sorting.Quicksort (scanUp scanDown part)

verified_compile compiled := [swap, scanUp, scanDown, part, find, select]

theorem select_export :
    ({ name := "select", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 7, the export `select`, called with an array that the caller hands over and a rank
`k`, from a heap with room for `compiled.select.bound`, returns without a trap `expected xs k`, the
word of rank `k`, and raises `top` by at most the bound. -/
theorem select_implements :
    ImplementsA false compiled.module 7
      (fun x : Moved (Array UInt64) × UInt64 => expected x.1.val x.2)
      (fun x heap store => heap.Within store compiled.module (compiled.select.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.select.bound x) :=
  Verified.implementsA_congr compiled.select.trapFree fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ =>
    select_eq x.1.val x.2 (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The generated bound is 0, so a call does not raise `top`. -/
theorem select_bound (xs : Array UInt64) (k : UInt64) :
    compiled.select.bound ({ val := xs }, k) = 0 :=
  compiled.select.bound_eq xs k

#print axioms select_implements

end Library.Sorting.Find
