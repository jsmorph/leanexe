import Library.Sorting.Heapsort.Compiled
import Verified.Master

namespace Library.Sorting.Heapsort

open LeanExe.Pipeline

/-- The export `heapsort`, called on an array of words that the caller moves, returns the array
of its elements in nondecreasing order, as `List.mergeSort` orders them. -/
theorem heapsort_master :
    Verified.Master compiled.module compiled.tables "heapsort" compiled.heapsort.bound
      (fun _ => True)
      (fun (xs : Moved (Array UInt64)) ys => ys = (xs.val.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.heapsort.trapFree) nofun heapsort_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => heapsort_eq xs.val hxs.values.size_lt

#print axioms heapsort_master

end Library.Sorting.Heapsort
