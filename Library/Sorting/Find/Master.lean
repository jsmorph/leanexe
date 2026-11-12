import Library.Sorting.Find.Compiled
import Verified.Master

namespace Library.Sorting.Find

open LeanExe.Pipeline

theorem getElem!_toArray_eq_getD (l : List UInt64) (k : Nat) : l.toArray[k]! = l.getD k 0 :=
  List.getElem!_toArray.trans (List.getElem!_eq_getElem?_getD.trans List.getD_eq_getElem?_getD.symm)

/-- The export `select`, called on an array of words that the caller moves and a position `k`,
returns the word at position `k` of the array's elements in nondecreasing order, as
`List.mergeSort` orders them, and 0 when `k` is not below the size of the array. -/
theorem select_master :
    Verified.Master compiled.module compiled.tables "select" compiled.select.bound (fun _ => True)
      (fun (x : Moved (Array UInt64) × UInt64) y =>
        y = (x.1.val.toList.mergeSort (· ≤ ·)).getD x.2.toNat 0) :=
  .of_trapFree (.ofA compiled.select.trapFree) nofun select_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ =>
      (select_eq x.1.val x.2 hxs.values.size_lt).trans (getElem!_toArray_eq_getD _ _)

#print axioms select_master

end Library.Sorting.Find
