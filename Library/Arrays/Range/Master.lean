import Library.Arrays.Range.Compiled
import LeanExe.Dialect.Lemmas
import Verified.Master

namespace Library.Arrays.Range

open LeanExe.Dialect

theorem evens_export :
    ({ name := "evens", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `evens n` has `n` elements, and element `i` is `2 * i` modulo `2 ^ 64`. -/
theorem evens_eq (n : UInt64) :
    evens n = ((List.range n.toNat).map fun i => 2 * UInt64.ofNat i).toArray := by
  have hl : (evens n).toList = (List.range n.toNat).map fun i => 2 * UInt64.ofNat i :=
    loop_induction (n := n) (init := LeanExe.build 0 fun _ => (0 : UInt64))
      (f := fun i acc => acc.push (2 * i))
      (fun m acc => acc.toList = (List.range m).map fun i => 2 * UInt64.ofNat i)
      (by simp [LeanExe.build])
      fun m acc _ hacc => by
        rw [Array.toList_push, hacc, List.range_succ, List.map_append]
        rfl
  exact Array.toList_inj.mp hl

/-- The export `evens`, called on a count `n`, returns the array of `n` words whose element `i` is
`2 * i` modulo `2 ^ 64`. -/
theorem evens_master :
    Verified.Master compiled.module compiled.tables "evens" compiled.evens.bound (fun _ => True)
      (fun (n : UInt64) y => y = ((List.range n.toNat).map fun i => 2 * UInt64.ofNat i).toArray) :=
  .of_trapFree (.ofA compiled.evens.trapFree) nofun evens_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ n _ _ => evens_eq n

#print axioms evens_master

end Library.Arrays.Range
