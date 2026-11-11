import Library.Sorting.StraightInsertion.Compiled
import Verified.Master

namespace Library.Sorting.StraightInsertion

open LeanExe.Pipeline

/-- The export `straightInsertion`, called on an array of words that the caller moves, returns
the array of its elements in nondecreasing order, as `List.mergeSort` orders them. -/
theorem straightInsertion_master :
    Verified.Master compiled.module compiled.tables "straightInsertion"
      compiled.straightInsertion.bound (fun _ => True)
      (fun (xs : Moved (Array UInt64)) ys => ys = (xs.val.toList.mergeSort (· ≤ ·)).toArray) :=
  .of_trapFree (.ofA compiled.straightInsertion.trapFree) nofun straightInsertion_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ _ => straightInsertion_eq xs.val hxs.values.size_lt

#print axioms straightInsertion_master

end Library.Sorting.StraightInsertion
