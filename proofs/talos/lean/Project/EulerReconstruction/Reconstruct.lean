import Project.EulerReconstruction.Limit

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction

set_option maxHeartbeats 400000 in
theorem reconstruct_exact (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64)
    (left center right : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 40 initial
      (stateValues right ++ stateValues center ++ stateValues left ++ [.i64 fuel])
      (fun final values => final = initial ∧
        values = facesValues (reconstruct fuel.toNat left center right)) := by
  refine TerminatesWith.of_wp_entry_for (f := func40Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func40 _ initial
    (func40Def.toLocals [.i64 fuel,
      .i64 left.density, .i64 left.mx, .i64 left.my, .i64 left.energy,
      .i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy,
      .i64 right.density, .i64 right.mx, .i64 right.my, .i64 right.energy]) env
  unfold func40
  wp_run [func40Def]
  guard_peel
  cases hl : admissibleState left
  all_goals guard_call (admissible_exact env initial left)
  · reconstruction_call (rejected_faces_exact env initial)
    simp [reconstruct, hl, facesValues, stateValues]
  · cases hc : admissibleState center
    all_goals guard_call (admissible_exact env initial center)
    · reconstruction_call (rejected_faces_exact env initial)
      simp [reconstruct, hl, hc, facesValues, stateValues]
    · cases hr : admissibleState right
      all_goals guard_call (admissible_exact env initial right)
      · reconstruction_call (rejected_faces_exact env initial)
        simp [reconstruct, hl, hc, hr, facesValues, stateValues]
      · reconstruction_call (slope_exact env initial left center right)
        by_cases hs : (slope left center right).status = 0
        all_goals guard_peel
        · reconstruction_call (limit_exact env initial fuel center
            (slope left center right).state 0x3FE0000000000000)
          simp [reconstruct, hl, hc, hr, hs, facesValues, stateValues]
        · reconstruction_call (rejected_faces_exact env initial)
          simp [reconstruct, hl, hc, hr, hs, facesValues, stateValues]

#print axioms reconstruct_exact

end Project.EulerReconstruction.Execution
