import Library.Sorting.StraightInsertion.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of straight insertion.  The compiler translates the tail
recursion of `shift` into a loop, and `straightInsertion` consumes its array, which the caller
hands over as `Moved (Array UInt64)`: every update is the array's last use, so the module sorts the
array in its own block.  `straightInsertion_implements` composes the generated
`compiled.straightInsertion.trapFree` with `straightInsertion_eq`. -/

namespace Library.Sorting.StraightInsertion

open Wasm LeanExe.Pipeline

verified_compile compiled := [shift, straightInsertion]

theorem straightInsertion_export :
    ({ name := "straightInsertion", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, the export `straightInsertion`, called with an array that the caller hands over,
from a heap with room for `compiled.straightInsertion.bound`, returns without a trap the owned
array `expected xs`, the elements in nondecreasing order, and raises `top` by at most the bound. -/
theorem straightInsertion_implements :
    ImplementsA false compiled.module 3 (fun x : Moved (Array UInt64) => expected x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.straightInsertion.bound x))
      (fun x heap _ heap' _ =>
        heap'.top.toNat ≤ heap.top.toNat + compiled.straightInsertion.bound x) :=
  Verified.implementsA_congr compiled.straightInsertion.trapFree fun _ _ _ x ⟨_, _, hxs⟩ =>
    straightInsertion_eq x.val (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The module allocates nothing: it sorts the array in its own block. -/
theorem straightInsertion_bound (xs : Array UInt64) :
    compiled.straightInsertion.bound { val := xs } = 0 :=
  compiled.straightInsertion.bound_eq xs

#print axioms straightInsertion_implements

end Library.Sorting.StraightInsertion
