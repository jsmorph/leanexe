import Library.Combinatorics.NextPermutation.Compiled
import Verified.Master

namespace Library.Combinatorics.NextPermutation

open LeanExe.Pipeline (Moved)

/-- The export `nextPerm`, called on an array `xs` that the caller moves, returns the flag 1 and
the least arrangement of `xs` greater than `xs` in the lexicographic order when one exists, and
otherwise the flag 0 and the words of `xs` in nondecreasing order. -/
theorem nextPerm_master :
    Verified.Master compiled.module compiled.tables "nextPerm" compiled.nextPerm.bound
      (fun _ => True) (fun (x : Moved (Array UInt64)) y => IsNext x.val y) :=
  .of_trapFree (.ofA compiled.nextPerm.trapFree) nofun nextPerm_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, hxs⟩ _ => nextPerm_isNext x.val hxs.values.size_lt

#print axioms nextPerm_master

end Library.Combinatorics.NextPermutation
