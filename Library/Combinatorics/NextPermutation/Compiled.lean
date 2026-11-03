import Library.Combinatorics.NextPermutation.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of the next arrangement.  By the compiler's rules, which the
verified compiler's manual states, the compiler translates the tail recursions of `ascent`,
`lastAbove`, and `reverseRange` into loops, so no theorem of the module has a call-depth premise.
`nextPerm` consumes its array, which the caller hands over as `Moved (Array UInt64)`, and returns
the flag and the array, and the generated bound is 0.  `nextPerm_implements` is the generated
`compiled.nextPerm.trapFree`: the module returns `nextPerm xs`.  `nextPerm_isNext` of the proof
states that `nextPerm xs` is the pair that `IsNext xs` specifies when `xs` has fewer than `2^64`
words, which every array that the representation of a call holds has, and no theorem joins the two.
-/

namespace Library.Combinatorics.NextPermutation

open Wasm LeanExe.Pipeline
open Library.Sorting.Heapsort (swap)

verified_compile compiled := [swap, ascent, lastAbove, reverseRange, nextPerm]

theorem nextPerm_export :
    ({ name := "nextPerm", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 6, the export `nextPerm`, called with an array that the caller hands over, from a heap
with room for `compiled.nextPerm.bound`, returns without a trap the flag and the owned array of
`nextPerm xs`, and raises `top` by at most the bound. -/
theorem nextPerm_implements :
    ImplementsA false compiled.module 6 (fun x : Moved (Array UInt64) => nextPerm x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.nextPerm.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.nextPerm.bound x) :=
  compiled.nextPerm.trapFree

/-- The generated bound is 0, so a call does not raise `top`. -/
theorem nextPerm_bound (xs : Array UInt64) : compiled.nextPerm.bound { val := xs } = 0 :=
  compiled.nextPerm.bound_eq xs

#print axioms nextPerm_implements
#print axioms nextPerm_isNext

end Library.Combinatorics.NextPermutation
