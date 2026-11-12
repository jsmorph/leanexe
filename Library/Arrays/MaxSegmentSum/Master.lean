import Library.Arrays.MaxSegmentSum.Compiled
import Library.Arrays.MaxSegmentSum.Proof
import Verified.Master

namespace Library.Arrays.MaxSegmentSum

theorem mss_export :
    ({ name := "mss", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `mss`, called on an array of `Int64` values whose absolute values sum to less than
`2 ^ 63`, returns the value whose integer is the greatest sum of a segment of the values read as
integers, from 0 for the empty segment. -/
theorem mss_master :
    Verified.Master compiled.module compiled.tables "mss" compiled.mss.bound
      (fun (xs : Array Int64) => (xs.toList.map fun x => x.toInt.natAbs).sum < 2 ^ 63)
      (fun (xs : Array Int64) (y : Int64) => y.toInt =
        (((xs.toList.map Int64.toInt).inits.map List.tails).flatten.map List.sum).foldr max 0) :=
  .of_trapFree (.ofA compiled.mss.trapFree) nofun mss_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hD => mss_toInt x hD

#print axioms mss_master

end Library.Arrays.MaxSegmentSum
