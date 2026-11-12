import Library.Sorting.MergeSort.Compiled
import Verified.Master

namespace Library.Sorting.MergeSort

open LeanExe.Pipeline

/-- The export `mergeSort`, called on an array of words that the caller moves, returns the array
of its elements in nondecreasing order, as `List.mergeSort` orders them. -/
theorem mergeSort_master :
    Verified.Master compiled.module compiled.tables "mergeSort" compiled.mergeSort.bound
      (fun _ => True)
      (fun (xs : Moved (Array UInt64)) ys => ys = (xs.val.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.mergeSort.trapFree) nofun mergeSort_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => mergeSort_eq xs.val hxs.values.size_lt

#print axioms mergeSort_master

end Library.Sorting.MergeSort
