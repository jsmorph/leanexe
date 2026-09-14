import Project.EulerReconstruction.Minmod

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction

theorem slope_exact (env : HostEnv Unit) (initial : Store Unit) (left center right : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 30 initial
      (stateValues right ++ stateValues center ++ stateValues left)
      (fun final values => final = initial ∧ values = slopeValues (slope left center right)) := by
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func30 _ initial
    (func30Def.toLocals [.i64 left.density, .i64 left.mx, .i64 left.my, .i64 left.energy,
      .i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy,
      .i64 right.density, .i64 right.mx, .i64 right.my, .i64 right.energy]) env
  unfold func30
  wp_run [func30Def]
  guard_peel
  reconstruction_call (difference_exact env initial center left)
  reconstruction_call (difference_exact env initial right center)
  cases hb : finiteState (difference center left)
  all_goals guard_call (finite_state_exact env initial (difference center left))
  · reconstruction_call (rejected_slope_exact env initial)
    simp [slope, hb, stateValues, slopeValues]
  · cases hf : finiteState (difference right center)
    all_goals guard_call (finite_state_exact env initial (difference right center))
    · reconstruction_call (rejected_slope_exact env initial)
      simp [slope, hb, hf, stateValues, slopeValues]
    · reconstruction_call (minmod_state_exact env initial
        (difference center left) (difference right center))
      simp [slope, hb, hf, stateValues, slopeValues]

#print axioms slope_exact

end Project.EulerReconstruction.Execution
