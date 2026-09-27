import Project.EulerReconstruction.Loop

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction
open Project.EulerConservative.Execution (boolWord)

def facesPost (initial : Store Unit) (output : Faces) : Assertion Unit
  | .Fallthrough final frame => final = initial ∧ frame.values = facesValues output
  | _ => False

theorem limit_return_spec (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (fuel : UInt64) (center delta : State)
    (factor : UInt64) (output : Faces) (done : Bool)
    (hFrame : LimitFrameAt frame fuel center delta factor output done) :
    wp Project.EulerReconstruction.«module» (func38.drop 3)
      (facesPost initial (if done then output else constantFaces center)) initial frame env := by
  cases done
  all_goals
    rcases hFrame with ⟨hParams, hLocals, hValues, hStatus, hLd, hLx, hLy,
      hLe, hRd, hRx, hRy, hRe, hFactor, hDone⟩
    rcases frame with ⟨params, locals, values⟩
    dsimp only at hParams hLocals hValues ⊢
    subst params
    subst values
    dsimp only at *
    limit_peel
  · refine wp_call_tw (constant_exact env initial center) ?_
    rintro st values ⟨hst, hValues⟩
    subst st
    simp only [facesValues] at hValues
    subst values
    limit_peel
    simp [facesPost, facesValues, constantFaces]
  · simp_all [facesPost, facesValues]

#print axioms limit_return_spec

end Project.EulerReconstruction.Execution
