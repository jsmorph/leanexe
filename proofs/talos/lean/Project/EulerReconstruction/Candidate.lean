import Project.EulerReconstruction.Slope

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction
open Project.ProofKit.F64Order (finiteBits)

theorem candidate_exact (env : HostEnv Unit) (initial : Store Unit)
    (center delta : State) (factor : UInt64) :
    TerminatesWith env Project.EulerReconstruction.«module» 36 initial
      ([.i64 factor] ++ stateValues delta ++ stateValues center)
      (fun final values => final = initial ∧ values = facesValues (candidate center delta factor)) := by
  refine TerminatesWith.of_wp_entry_for (f := func36Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func36 _ initial
    (func36Def.toLocals [.i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy,
      .i64 delta.density, .i64 delta.mx, .i64 delta.my, .i64 delta.energy, .i64 factor]) env
  unfold func36
  wp_run [func36Def]
  guard_peel
  reconstruction_call (scale_exact env initial factor delta)
  reconstruction_call (difference_exact env initial center (scale factor delta))
  reconstruction_call (sum_exact env initial center (scale factor delta))
  cases hf : finiteBits factor
  all_goals guard_call (finite_exact env initial factor)
  · reconstruction_call (rejected_faces_exact env initial)
    simp [candidate, hf, stateValues, facesValues]
  · cases ho : finiteState (scale factor delta)
    all_goals guard_call (finite_state_exact env initial (scale factor delta))
    · reconstruction_call (rejected_faces_exact env initial)
      simp [candidate, hf, ho, stateValues, facesValues]
    · cases hl : admissibleState (difference center (scale factor delta))
      all_goals guard_call (admissible_exact env initial (difference center (scale factor delta)))
      · reconstruction_call (rejected_faces_exact env initial)
        simp [candidate, hf, ho, hl, stateValues, facesValues]
      · cases hr : admissibleState (sum center (scale factor delta))
        all_goals guard_call (admissible_exact env initial (sum center (scale factor delta)))
        · reconstruction_call (rejected_faces_exact env initial)
          simp [candidate, hf, ho, hl, hr, stateValues, facesValues]
        · simp [candidate, hf, ho, hl, hr, stateValues, facesValues]

#print axioms candidate_exact

end Project.EulerReconstruction.Execution
