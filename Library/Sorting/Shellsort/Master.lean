import Library.Sorting.Shellsort.Compiled
import Verified.Master

namespace Library.Sorting.Shellsort

open LeanExe.Pipeline

/-- The export `shellsort`, called on an array of words that the caller moves, returns the array
of its elements in nondecreasing order, as `List.mergeSort` orders them. -/
theorem shellsort_master :
    Verified.Master compiled.module compiled.tables "shellsort" compiled.shellsort.bound
      (fun _ => True)
      (fun (xs : Moved (Array UInt64)) ys => ys = (xs.val.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.shellsort.trapFree) nofun shellsort_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => shellsort_eq xs.val hxs.values.size_lt

#print axioms shellsort_master

end Library.Sorting.Shellsort
