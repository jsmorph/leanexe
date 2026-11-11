import Library.Sorting.Insertion.Compiled
import Verified.Master

namespace Library.Sorting.Insertion

/-- The export `sortInsert`, called on an array of words, returns the array of its elements in
nondecreasing order, as `List.mergeSort` orders them. -/
theorem sortInsert_master :
    Verified.Master compiled.module compiled.tables "sortInsert" compiled.sortInsert.bound
      (fun _ => True)
      (fun (xs : Array UInt64) ys => ys = (xs.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.sortInsert.trapFree) nofun sortInsert_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ _ => sortInsert_eq x (show _ < 2 ^ 64 from hxs.values.size_lt)

#print axioms sortInsert_master

end Library.Sorting.Insertion
