import Examples.RunningMax.Program
import Examples.RunningMax.Spec

/-! The program equals the specification, a fact about the Lean definitions that the verified
compiler's call theorem uses. -/

namespace Examples.RunningMax

/-- The program's fold over a list, from the largest entry `m` so far and the result `out` so far,
appends to `out` the largest of `m` and each nonempty prefix of the list. -/
theorem foldl_largest (l : List UInt64) (m : UInt64) (out : Array UInt64) :
    (l.foldl (fun (state : UInt64 × Array UInt64) x =>
      let largest := max state.1 x
      (largest, state.2.push largest)) (m, out)).2.toList =
      out.toList ++ (List.range l.length).map fun i => (l.take (i + 1)).foldl max m := by
  induction l generalizing m out with
  | nil => simp
  | cons x t ih =>
    rw [List.foldl_cons]
    dsimp only
    rw [ih]
    simp [List.range_succ_eq_map, List.map_map, Function.comp_def, List.take_succ_cons]

/-- The program computes the specification on every input. -/
theorem compute_eq (xs : Array UInt64) : compute xs = expected xs := by
  apply Array.toList_inj.mp
  rw [compute, ← Array.foldl_toList, foldl_largest]
  simp [expected, largestThrough]

end Examples.RunningMax
