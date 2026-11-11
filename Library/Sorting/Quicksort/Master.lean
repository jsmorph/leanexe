import Library.Sorting.Quicksort.Compiled
import Verified.Master

namespace Library.Sorting.Quicksort

open LeanExe.Pipeline

/-- The export `quicksort`, called on an array of words that the caller moves, returns the array
of its elements in nondecreasing order, as `List.mergeSort` orders them. -/
theorem quicksort_master :
    Verified.Master compiled.module compiled.tables "quicksort" compiled.quicksort.bound
      (fun _ => True)
      (fun (xs : Moved (Array UInt64)) ys => ys = (xs.val.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.quicksort.trapFree) nofun quicksort_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => quicksort_eq xs.val hxs.values.size_lt

#print axioms quicksort_master

end Library.Sorting.Quicksort
