import Library.Sorting.RadixSort.Proof
import Verified.Reflect.Command
import Verified.Congr

/-! The verified compiler's module of radix sort.  By the compiler's rules, which the verified
compiler's manual states, the compiler translates the loops of `countDigits` and `distribute` and
the tail recursion of `passes` into loops, so no theorem of the module has a call-depth premise.
`radixSort` consumes its array, which the caller hands over as `Moved (Array UInt64)`, and builds a
second array of the same size and an array of 256 counts.  `radixSort_implements` composes the
generated `compiled.radixSort.trapFree` with `radixSort_eq`, and `radixSort_bound` states the
generated bound as `blockCost n + blockCost 256`, the costs of the program's two builds. -/

namespace Library.Sorting.RadixSort

open Wasm LeanExe.Pipeline LeanExe.Dialect

verified_compile compiled := [digit, countDigits, distribute, passes, radixSort]

theorem radixSort_export :
    ({ name := "radixSort", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 6, the export `radixSort`, called with an array that the caller hands over, from a heap
with room for `compiled.radixSort.bound`, returns without a trap the owned array `expected xs`, the
elements in nondecreasing order, and raises `top` by at most the bound. -/
theorem radixSort_implements :
    ImplementsA false compiled.module 6 (fun x : Moved (Array UInt64) => expected x.val)
      (fun x heap store => heap.Within store compiled.module (compiled.radixSort.bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + compiled.radixSort.bound x) :=
  Verified.implementsA_congr compiled.radixSort.trapFree fun _ _ _ x ⟨_, _, hxs⟩ =>
    radixSort_eq x.val (show _ < 2 ^ 64 from hxs.values.size_lt)

/-- The generated bound is a block of the array's size and a block of 256 counts. -/
theorem radixSort_bound (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    compiled.radixSort.bound { val := xs } =
      Verified.blockCost xs.size + Verified.blockCost 256 := by
  rw [compiled.radixSort.bound_eq, size_toUInt64 xs hsize]
  rfl

#print axioms radixSort_implements

end Library.Sorting.RadixSort
