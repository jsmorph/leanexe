import Library.Sorting.RadixSort.Compiled
import Verified.Master

namespace Library.Sorting.RadixSort

open LeanExe.Pipeline

/-- The export `radixSort`, called on an array of words that the caller moves, returns the array
of its elements in nondecreasing order, as `List.mergeSort` orders them. -/
theorem radixSort_master :
    Verified.Master compiled.module compiled.tables "radixSort" compiled.radixSort.bound
      (fun _ => True)
      (fun (xs : Moved (Array UInt64)) ys => ys = (xs.val.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.radixSort.trapFree) nofun radixSort_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => radixSort_eq xs.val hxs.values.size_lt

#print axioms radixSort_master

end Library.Sorting.RadixSort
