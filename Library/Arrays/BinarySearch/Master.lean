import Library.Arrays.BinarySearch.Compiled
import Verified.Master

namespace Library.Arrays.BinarySearch

/-- The export `lowerBound`, called on an array of words sorted in nondecreasing order and a key,
returns the number of elements less than the key, which is the least index whose element is at
least the key, or the size of the array when no element is. -/
theorem lowerBound_master :
    Verified.Master compiled.module compiled.tables "lowerBound" compiled.lowerBound.bound
      (fun x : Array UInt64 × UInt64 => ∀ i j, i ≤ j → j < x.1.size → x.1[i]! ≤ x.1[j]!)
      (fun x y => y = UInt64.ofNat (x.1.toList.countP (· < x.2))) :=
  .of_trapFree (.ofA compiled.lowerBound.trapFree) nofun lowerBound_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ hs => lowerBound_eq x.1 x.2 hs hxs.values.size_lt

#print axioms lowerBound_master

end Library.Arrays.BinarySearch
