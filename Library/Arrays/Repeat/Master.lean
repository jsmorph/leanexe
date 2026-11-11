import Library.Arrays.Repeat.Compiled
import LeanExe.Dialect.Lemmas
import Verified.Master

namespace Library.Arrays.Repeat

open LeanExe.Dialect

theorem repeated_export :
    ({ name := "repeated", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- `repeated xs n` is `n` copies of `xs`, one after another. -/
theorem repeated_eq (xs : Array UInt64) (n : UInt64) :
    repeated xs n = (List.replicate n.toNat xs.toList).flatten.toArray := by
  have hl : (repeated xs n).toList = (List.replicate n.toNat xs.toList).flatten :=
    loop_induction (n := n) (init := LeanExe.build 0 fun _ => (0 : UInt64))
      (f := fun _ acc => acc ++ xs)
      (fun m acc => acc.toList = (List.replicate m xs.toList).flatten) (by simp [LeanExe.build])
      fun m acc _ hacc => by
        rw [Array.toList_append, hacc, List.replicate_succ', List.flatten_append]
        simp
  exact Array.toList_inj.mp hl

/-- The export `repeated`, called on an array of words and a count `n`, returns `n` copies of the
array, one after another. -/
theorem repeated_master :
    Verified.Master compiled.module compiled.tables "repeated" compiled.repeated.bound
      (fun _ => True)
      (fun (x : Array UInt64 × UInt64) y =>
        y = (List.replicate x.2.toNat x.1.toList).flatten.toArray) :=
  .of_trapFree (.ofA compiled.repeated.trapFree) nofun repeated_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => repeated_eq x.1 x.2

#print axioms repeated_master

end Library.Arrays.Repeat
