import Project.EulerOutwardMaximum.Speed
import Project.EulerRiemann.OutwardMaximum

namespace Project.EulerOutwardMaximum.Execution
open Wasm
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.ProofKit.F64Outward (Checked rejected)
open Project.EulerRiemann.OutwardMaximum (merge)

theorem merge_exact (env : HostEnv Unit) (initial : Store Unit) (left right : Checked) :
    TerminatesWith env Project.EulerOutwardMaximum.«module» 3 initial
      [.i64 right.value, .i64 right.status, .i64 left.value, .i64 left.status]
      (fun final values => final = initial ∧ values = checkedValues (merge left right)) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardMaximum.«module» func3 _ initial
    (func3Def.toLocals [.i64 left.status, .i64 left.value, .i64 right.status, .i64 right.value]) env
  unfold func3
  wp_run [func3Def]
  by_cases hl : left.status = 0
  · by_cases hr : right.status = 0
    · have hm : max left.value right.value =
          (if left.value ≤ right.value then right.value else left.value) := rfl
      by_cases hv : left.value ≤ right.value <;> guard_peel <;>
        simp [merge, hl, hr, checkedValues, hm, hv]
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [merge, hl, hr, checkedValues, rejected]
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [merge, hl, checkedValues, rejected]

#print axioms merge_exact
end Project.EulerOutwardMaximum.Execution
