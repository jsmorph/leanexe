import Library.Strings.Kmp.Compiled
import Verified.Master

namespace Library.Strings.Kmp

/-- The export `occurrences`, called on a pattern array `pat`, its byte count `m`, a text array
`txt`, and its byte count `n`, returns in increasing order the positions `i ≤ n` at which the `m`
bytes of the pattern occur in the `n` bytes of the text. -/
theorem occurrences_master :
    Verified.Master compiled.module compiled.tables "occurrences" compiled.occurrences.bound
      (fun _ => True)
      (fun (x : Array UInt64 × UInt64 × Array UInt64 × UInt64) (y : Array UInt64) =>
        y = (((List.range (x.2.2.2.toNat + 1)).filter fun i =>
          decide (OccursAt x.1 x.2.1.toNat x.2.2.1 x.2.2.2.toNat i)).map UInt64.ofNat).toArray) :=
  .of_trapFree (.ofA compiled.occurrences.trapFree) nofun occurrences_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => occurrences_eq x.1 x.2.1 x.2.2.1 x.2.2.2

#print axioms occurrences_master

end Library.Strings.Kmp
