import Library.Numerics.Reductions.Word.Compiled
import Verified.Master

namespace Library.Numerics.Reductions.Word

theorem sumArray_export :
    ({ name := "sumArray", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem productArray_export :
    ({ name := "productArray", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem xorArray_export :
    ({ name := "xorArray", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sumArray_eq (xs : Array UInt64) : sumArray xs = xs.toList.sum := by
  rw [sumArray, ← Array.foldl_toList, List.sum_eq_foldl]

theorem productArray_eq (xs : Array UInt64) : productArray xs = xs.toList.prod := by
  rw [productArray, ← Array.foldl_toList, List.prod_eq_foldl]

theorem xorArray_eq (xs : Array UInt64) : xorArray xs = xs.toList.foldl (· ^^^ ·) 0 := by
  rw [xorArray, ← Array.foldl_toList]

/-- The export `sumArray`, called on an array of words, returns the sum of its elements in
`UInt64`, that is, modulo `2 ^ 64`. -/
theorem sumArray_master :
    Verified.Master compiled.module compiled.tables "sumArray" compiled.sumArray.bound
      (fun _ => True) (fun (xs : Array UInt64) y => y = xs.toList.sum) :=
  .of_trapFree (.ofA compiled.sumArray.trapFree) nofun sumArray_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => sumArray_eq x

#print axioms sumArray_master

/-- The export `productArray`, called on an array of words, returns the product of its elements in
`UInt64`, that is, modulo `2 ^ 64`, and 1 for the empty array. -/
theorem productArray_master :
    Verified.Master compiled.module compiled.tables "productArray" compiled.productArray.bound
      (fun _ => True) (fun (xs : Array UInt64) y => y = xs.toList.prod) :=
  .of_trapFree (.ofA compiled.productArray.trapFree) nofun productArray_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => productArray_eq x

#print axioms productArray_master

/-- The export `xorArray`, called on an array of words, returns the bitwise exclusive or of its
elements, and 0 for the empty array. -/
theorem xorArray_master :
    Verified.Master compiled.module compiled.tables "xorArray" compiled.xorArray.bound
      (fun _ => True) (fun (xs : Array UInt64) y => y = xs.toList.foldl (· ^^^ ·) 0) :=
  .of_trapFree (.ofA compiled.xorArray.trapFree) nofun xorArray_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => xorArray_eq x

#print axioms xorArray_master

end Library.Numerics.Reductions.Word
